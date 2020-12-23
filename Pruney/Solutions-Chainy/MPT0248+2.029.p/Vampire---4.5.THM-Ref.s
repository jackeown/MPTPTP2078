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
% DateTime   : Thu Dec  3 12:37:53 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 212 expanded)
%              Number of leaves         :   27 (  94 expanded)
%              Depth                    :    8
%              Number of atoms          :  265 ( 520 expanded)
%              Number of equality atoms :  100 ( 252 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f314,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f60,f69,f74,f79,f88,f93,f98,f118,f133,f172,f175,f194,f209,f225,f230,f242,f299,f310,f313])).

fof(f313,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f310,plain,
    ( ~ spl3_11
    | spl3_25 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl3_11
    | spl3_25 ),
    inference(subsumption_resolution,[],[f306,f117])).

fof(f117,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_11
  <=> sK1 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f306,plain,
    ( sK1 != k2_xboole_0(sK1,sK2)
    | spl3_25 ),
    inference(superposition,[],[f298,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f298,plain,
    ( sK1 != k2_xboole_0(sK2,sK1)
    | spl3_25 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl3_25
  <=> sK1 = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f299,plain,
    ( ~ spl3_25
    | ~ spl3_1
    | ~ spl3_11
    | spl3_18 ),
    inference(avatar_split_clause,[],[f263,f206,f115,f46,f296])).

fof(f46,plain,
    ( spl3_1
  <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f206,plain,
    ( spl3_18
  <=> k1_tarski(sK0) = k2_xboole_0(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f263,plain,
    ( sK1 != k2_xboole_0(sK2,sK1)
    | ~ spl3_1
    | ~ spl3_11
    | spl3_18 ),
    inference(backward_demodulation,[],[f207,f135])).

fof(f135,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f48,f117])).

fof(f48,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f207,plain,
    ( k1_tarski(sK0) != k2_xboole_0(sK2,k1_tarski(sK0))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f206])).

fof(f242,plain,
    ( spl3_4
    | spl3_8
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl3_4
    | spl3_8
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f240,f92])).

fof(f92,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_8
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f240,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | spl3_4
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f233,f193])).

fof(f193,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl3_16
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f233,plain,
    ( k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl3_4
    | ~ spl3_9
    | ~ spl3_21 ),
    inference(backward_demodulation,[],[f97,f228])).

fof(f228,plain,
    ( k1_xboole_0 = sK2
    | spl3_4
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f226,f64])).

fof(f64,plain,
    ( sK2 != k1_tarski(sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_4
  <=> sK2 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f226,plain,
    ( sK2 = k1_tarski(sK0)
    | k1_xboole_0 = sK2
    | ~ spl3_21 ),
    inference(resolution,[],[f224,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f224,plain,
    ( r1_tarski(sK2,k1_tarski(sK0))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl3_21
  <=> r1_tarski(sK2,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f97,plain,
    ( k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_9
  <=> k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

% (9386)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f230,plain,
    ( spl3_2
    | spl3_4
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl3_2
    | spl3_4
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f228,f55])).

fof(f55,plain,
    ( k1_xboole_0 != sK2
    | spl3_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f225,plain,
    ( spl3_21
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f211,f206,f222])).

fof(f211,plain,
    ( r1_tarski(sK2,k1_tarski(sK0))
    | ~ spl3_18 ),
    inference(superposition,[],[f28,f208])).

fof(f208,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK2,k1_tarski(sK0))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f206])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f209,plain,
    ( spl3_18
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f189,f130,f95,f206])).

fof(f130,plain,
    ( spl3_12
  <=> k4_xboole_0(k1_tarski(sK0),sK2) = k4_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f189,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK2,k1_tarski(sK0))
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f188,f97])).

fof(f188,plain,
    ( k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(sK2,k1_tarski(sK0))
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f187,f29])).

fof(f187,plain,
    ( k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k1_tarski(sK0))
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f186,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f186,plain,
    ( k2_xboole_0(sK2,k1_tarski(sK0)) = k5_xboole_0(sK2,k4_xboole_0(k1_xboole_0,sK2))
    | ~ spl3_12 ),
    inference(superposition,[],[f33,f132])).

fof(f132,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK2) = k4_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f194,plain,
    ( spl3_16
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f184,f169,f191])).

fof(f169,plain,
    ( spl3_15
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

% (9380)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f184,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f182,f26])).

fof(f26,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f182,plain,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_15 ),
    inference(superposition,[],[f33,f171])).

fof(f171,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f169])).

fof(f175,plain,
    ( ~ spl3_5
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl3_5
    | spl3_10 ),
    inference(subsumption_resolution,[],[f173,f25])).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f173,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_5
    | spl3_10 ),
    inference(forward_demodulation,[],[f106,f67])).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f106,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_10
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f172,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f161,f105,f66,f169])).

fof(f161,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f142,f67])).

fof(f142,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl3_10 ),
    inference(resolution,[],[f107,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f107,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f133,plain,
    ( spl3_12
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f120,f66,f46,f130])).

fof(f120,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK2) = k4_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f50,f67])).

fof(f50,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f32,f48])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f118,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f100,f57,f46,f115])).

fof(f57,plain,
    ( spl3_3
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f100,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f48,f58])).

fof(f58,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f98,plain,
    ( spl3_9
    | ~ spl3_1
    | spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f83,f76,f57,f46,f95])).

fof(f76,plain,
    ( spl3_7
  <=> r1_tarski(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f83,plain,
    ( k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_1
    | spl3_3
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f48,f82])).

fof(f82,plain,
    ( k1_xboole_0 = sK1
    | spl3_3
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f80,f59])).

fof(f59,plain,
    ( sK1 != k1_tarski(sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f80,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1
    | ~ spl3_7 ),
    inference(resolution,[],[f78,f35])).

fof(f78,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f93,plain,
    ( ~ spl3_8
    | spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f85,f76,f57,f90])).

fof(f85,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | spl3_3
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f59,f82])).

fof(f88,plain,
    ( spl3_5
    | spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f82,f76,f57,f66])).

fof(f79,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f51,f46,f76])).

fof(f51,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl3_1 ),
    inference(superposition,[],[f28,f48])).

fof(f74,plain,
    ( ~ spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f44,f57,f71])).

fof(f71,plain,
    ( spl3_6
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f44,plain,
    ( sK1 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f22])).

fof(f22,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f69,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f21,f66,f62])).

fof(f21,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f20,f57,f53])).

fof(f20,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:10:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.50  % (9388)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.50  % (9402)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.51  % (9395)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.51  % (9394)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.51  % (9383)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.51  % (9384)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.52  % (9403)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.52  % (9375)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.52  % (9376)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.52  % (9375)Refutation not found, incomplete strategy% (9375)------------------------------
% 0.19/0.52  % (9375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (9375)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (9375)Memory used [KB]: 1663
% 0.19/0.52  % (9375)Time elapsed: 0.123 s
% 0.19/0.52  % (9375)------------------------------
% 0.19/0.52  % (9375)------------------------------
% 0.19/0.53  % (9379)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.53  % (9382)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.53  % (9395)Refutation found. Thanks to Tanya!
% 0.19/0.53  % SZS status Theorem for theBenchmark
% 0.19/0.53  % (9400)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.53  % (9379)Refutation not found, incomplete strategy% (9379)------------------------------
% 0.19/0.53  % (9379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (9379)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (9379)Memory used [KB]: 6268
% 0.19/0.53  % (9379)Time elapsed: 0.129 s
% 0.19/0.53  % (9379)------------------------------
% 0.19/0.53  % (9379)------------------------------
% 0.19/0.53  % (9389)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.53  % (9396)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.53  % (9378)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.53  % (9384)Refutation not found, incomplete strategy% (9384)------------------------------
% 0.19/0.53  % (9384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (9384)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (9384)Memory used [KB]: 10746
% 0.19/0.53  % (9401)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.53  % (9384)Time elapsed: 0.128 s
% 0.19/0.53  % (9384)------------------------------
% 0.19/0.53  % (9384)------------------------------
% 0.19/0.53  % (9383)Refutation not found, incomplete strategy% (9383)------------------------------
% 0.19/0.53  % (9383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (9383)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (9383)Memory used [KB]: 10746
% 0.19/0.53  % (9383)Time elapsed: 0.130 s
% 0.19/0.53  % (9383)------------------------------
% 0.19/0.53  % (9383)------------------------------
% 0.19/0.53  % (9396)Refutation not found, incomplete strategy% (9396)------------------------------
% 0.19/0.53  % (9396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (9396)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (9396)Memory used [KB]: 1791
% 0.19/0.53  % (9396)Time elapsed: 0.141 s
% 0.19/0.53  % (9396)------------------------------
% 0.19/0.53  % (9396)------------------------------
% 0.19/0.53  % (9377)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.53  % SZS output start Proof for theBenchmark
% 0.19/0.53  fof(f314,plain,(
% 0.19/0.53    $false),
% 0.19/0.53    inference(avatar_sat_refutation,[],[f49,f60,f69,f74,f79,f88,f93,f98,f118,f133,f172,f175,f194,f209,f225,f230,f242,f299,f310,f313])).
% 0.19/0.53  fof(f313,plain,(
% 0.19/0.53    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0) | sK1 = sK2),
% 0.19/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.53  fof(f310,plain,(
% 0.19/0.53    ~spl3_11 | spl3_25),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f309])).
% 0.19/0.53  fof(f309,plain,(
% 0.19/0.53    $false | (~spl3_11 | spl3_25)),
% 0.19/0.53    inference(subsumption_resolution,[],[f306,f117])).
% 0.19/0.53  fof(f117,plain,(
% 0.19/0.53    sK1 = k2_xboole_0(sK1,sK2) | ~spl3_11),
% 0.19/0.53    inference(avatar_component_clause,[],[f115])).
% 0.19/0.53  fof(f115,plain,(
% 0.19/0.53    spl3_11 <=> sK1 = k2_xboole_0(sK1,sK2)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.53  fof(f306,plain,(
% 0.19/0.53    sK1 != k2_xboole_0(sK1,sK2) | spl3_25),
% 0.19/0.53    inference(superposition,[],[f298,f29])).
% 0.19/0.53  fof(f29,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f1])).
% 0.19/0.53  fof(f1,axiom,(
% 0.19/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.53  fof(f298,plain,(
% 0.19/0.53    sK1 != k2_xboole_0(sK2,sK1) | spl3_25),
% 0.19/0.53    inference(avatar_component_clause,[],[f296])).
% 0.19/0.53  fof(f296,plain,(
% 0.19/0.53    spl3_25 <=> sK1 = k2_xboole_0(sK2,sK1)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.19/0.53  fof(f299,plain,(
% 0.19/0.53    ~spl3_25 | ~spl3_1 | ~spl3_11 | spl3_18),
% 0.19/0.53    inference(avatar_split_clause,[],[f263,f206,f115,f46,f296])).
% 0.19/0.53  fof(f46,plain,(
% 0.19/0.53    spl3_1 <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.53  fof(f206,plain,(
% 0.19/0.53    spl3_18 <=> k1_tarski(sK0) = k2_xboole_0(sK2,k1_tarski(sK0))),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.19/0.53  fof(f263,plain,(
% 0.19/0.53    sK1 != k2_xboole_0(sK2,sK1) | (~spl3_1 | ~spl3_11 | spl3_18)),
% 0.19/0.53    inference(backward_demodulation,[],[f207,f135])).
% 0.19/0.53  fof(f135,plain,(
% 0.19/0.53    sK1 = k1_tarski(sK0) | (~spl3_1 | ~spl3_11)),
% 0.19/0.53    inference(backward_demodulation,[],[f48,f117])).
% 0.19/0.53  fof(f48,plain,(
% 0.19/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) | ~spl3_1),
% 0.19/0.53    inference(avatar_component_clause,[],[f46])).
% 0.19/0.53  fof(f207,plain,(
% 0.19/0.53    k1_tarski(sK0) != k2_xboole_0(sK2,k1_tarski(sK0)) | spl3_18),
% 0.19/0.53    inference(avatar_component_clause,[],[f206])).
% 0.19/0.53  fof(f242,plain,(
% 0.19/0.53    spl3_4 | spl3_8 | ~spl3_9 | ~spl3_16 | ~spl3_21),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f241])).
% 0.19/0.53  fof(f241,plain,(
% 0.19/0.53    $false | (spl3_4 | spl3_8 | ~spl3_9 | ~spl3_16 | ~spl3_21)),
% 0.19/0.53    inference(subsumption_resolution,[],[f240,f92])).
% 0.19/0.53  fof(f92,plain,(
% 0.19/0.53    k1_xboole_0 != k1_tarski(sK0) | spl3_8),
% 0.19/0.53    inference(avatar_component_clause,[],[f90])).
% 0.19/0.53  fof(f90,plain,(
% 0.19/0.53    spl3_8 <=> k1_xboole_0 = k1_tarski(sK0)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.53  fof(f240,plain,(
% 0.19/0.53    k1_xboole_0 = k1_tarski(sK0) | (spl3_4 | ~spl3_9 | ~spl3_16 | ~spl3_21)),
% 0.19/0.53    inference(forward_demodulation,[],[f233,f193])).
% 0.19/0.53  fof(f193,plain,(
% 0.19/0.53    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_16),
% 0.19/0.53    inference(avatar_component_clause,[],[f191])).
% 0.19/0.53  fof(f191,plain,(
% 0.19/0.53    spl3_16 <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.19/0.53  fof(f233,plain,(
% 0.19/0.53    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) | (spl3_4 | ~spl3_9 | ~spl3_21)),
% 0.19/0.53    inference(backward_demodulation,[],[f97,f228])).
% 0.19/0.53  fof(f228,plain,(
% 0.19/0.53    k1_xboole_0 = sK2 | (spl3_4 | ~spl3_21)),
% 0.19/0.53    inference(subsumption_resolution,[],[f226,f64])).
% 0.19/0.53  fof(f64,plain,(
% 0.19/0.53    sK2 != k1_tarski(sK0) | spl3_4),
% 0.19/0.53    inference(avatar_component_clause,[],[f62])).
% 0.19/0.53  fof(f62,plain,(
% 0.19/0.53    spl3_4 <=> sK2 = k1_tarski(sK0)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.53  fof(f226,plain,(
% 0.19/0.53    sK2 = k1_tarski(sK0) | k1_xboole_0 = sK2 | ~spl3_21),
% 0.19/0.53    inference(resolution,[],[f224,f35])).
% 0.19/0.53  fof(f35,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 0.19/0.53    inference(cnf_transformation,[],[f14])).
% 0.19/0.53  fof(f14,axiom,(
% 0.19/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.19/0.53  fof(f224,plain,(
% 0.19/0.53    r1_tarski(sK2,k1_tarski(sK0)) | ~spl3_21),
% 0.19/0.53    inference(avatar_component_clause,[],[f222])).
% 0.19/0.53  fof(f222,plain,(
% 0.19/0.53    spl3_21 <=> r1_tarski(sK2,k1_tarski(sK0))),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.19/0.53  fof(f97,plain,(
% 0.19/0.53    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) | ~spl3_9),
% 0.19/0.53    inference(avatar_component_clause,[],[f95])).
% 0.19/0.53  fof(f95,plain,(
% 0.19/0.53    spl3_9 <=> k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.53  % (9386)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.53  fof(f230,plain,(
% 0.19/0.53    spl3_2 | spl3_4 | ~spl3_21),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f229])).
% 0.19/0.53  fof(f229,plain,(
% 0.19/0.53    $false | (spl3_2 | spl3_4 | ~spl3_21)),
% 0.19/0.53    inference(subsumption_resolution,[],[f228,f55])).
% 0.19/0.53  fof(f55,plain,(
% 0.19/0.53    k1_xboole_0 != sK2 | spl3_2),
% 0.19/0.53    inference(avatar_component_clause,[],[f53])).
% 0.19/0.53  fof(f53,plain,(
% 0.19/0.53    spl3_2 <=> k1_xboole_0 = sK2),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.53  fof(f225,plain,(
% 0.19/0.53    spl3_21 | ~spl3_18),
% 0.19/0.53    inference(avatar_split_clause,[],[f211,f206,f222])).
% 0.19/0.53  fof(f211,plain,(
% 0.19/0.53    r1_tarski(sK2,k1_tarski(sK0)) | ~spl3_18),
% 0.19/0.53    inference(superposition,[],[f28,f208])).
% 0.19/0.53  fof(f208,plain,(
% 0.19/0.53    k1_tarski(sK0) = k2_xboole_0(sK2,k1_tarski(sK0)) | ~spl3_18),
% 0.19/0.53    inference(avatar_component_clause,[],[f206])).
% 0.19/0.53  fof(f28,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f8])).
% 0.19/0.53  fof(f8,axiom,(
% 0.19/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.19/0.53  fof(f209,plain,(
% 0.19/0.53    spl3_18 | ~spl3_9 | ~spl3_12),
% 0.19/0.53    inference(avatar_split_clause,[],[f189,f130,f95,f206])).
% 0.19/0.53  fof(f130,plain,(
% 0.19/0.53    spl3_12 <=> k4_xboole_0(k1_tarski(sK0),sK2) = k4_xboole_0(k1_xboole_0,sK2)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.19/0.53  fof(f189,plain,(
% 0.19/0.53    k1_tarski(sK0) = k2_xboole_0(sK2,k1_tarski(sK0)) | (~spl3_9 | ~spl3_12)),
% 0.19/0.53    inference(forward_demodulation,[],[f188,f97])).
% 0.19/0.53  fof(f188,plain,(
% 0.19/0.53    k2_xboole_0(k1_xboole_0,sK2) = k2_xboole_0(sK2,k1_tarski(sK0)) | ~spl3_12),
% 0.19/0.53    inference(forward_demodulation,[],[f187,f29])).
% 0.19/0.53  fof(f187,plain,(
% 0.19/0.53    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k1_tarski(sK0)) | ~spl3_12),
% 0.19/0.53    inference(forward_demodulation,[],[f186,f33])).
% 0.19/0.53  fof(f33,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f9])).
% 0.19/0.53  fof(f9,axiom,(
% 0.19/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.19/0.53  fof(f186,plain,(
% 0.19/0.53    k2_xboole_0(sK2,k1_tarski(sK0)) = k5_xboole_0(sK2,k4_xboole_0(k1_xboole_0,sK2)) | ~spl3_12),
% 0.19/0.53    inference(superposition,[],[f33,f132])).
% 0.19/0.53  fof(f132,plain,(
% 0.19/0.53    k4_xboole_0(k1_tarski(sK0),sK2) = k4_xboole_0(k1_xboole_0,sK2) | ~spl3_12),
% 0.19/0.53    inference(avatar_component_clause,[],[f130])).
% 0.19/0.53  fof(f194,plain,(
% 0.19/0.53    spl3_16 | ~spl3_15),
% 0.19/0.53    inference(avatar_split_clause,[],[f184,f169,f191])).
% 0.19/0.53  fof(f169,plain,(
% 0.19/0.53    spl3_15 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.19/0.54  % (9380)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.54  fof(f184,plain,(
% 0.19/0.54    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_15),
% 0.19/0.54    inference(forward_demodulation,[],[f182,f26])).
% 0.19/0.54  fof(f26,plain,(
% 0.19/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.54    inference(cnf_transformation,[],[f7])).
% 0.19/0.54  fof(f7,axiom,(
% 0.19/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.19/0.54  fof(f182,plain,(
% 0.19/0.54    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_15),
% 0.19/0.54    inference(superposition,[],[f33,f171])).
% 0.19/0.54  fof(f171,plain,(
% 0.19/0.54    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_15),
% 0.19/0.54    inference(avatar_component_clause,[],[f169])).
% 0.19/0.54  fof(f175,plain,(
% 0.19/0.54    ~spl3_5 | spl3_10),
% 0.19/0.54    inference(avatar_contradiction_clause,[],[f174])).
% 0.19/0.54  fof(f174,plain,(
% 0.19/0.54    $false | (~spl3_5 | spl3_10)),
% 0.19/0.54    inference(subsumption_resolution,[],[f173,f25])).
% 0.19/0.54  fof(f25,plain,(
% 0.19/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f5])).
% 0.19/0.54  fof(f5,axiom,(
% 0.19/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.19/0.54  fof(f173,plain,(
% 0.19/0.54    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl3_5 | spl3_10)),
% 0.19/0.54    inference(forward_demodulation,[],[f106,f67])).
% 0.19/0.54  fof(f67,plain,(
% 0.19/0.54    k1_xboole_0 = sK1 | ~spl3_5),
% 0.19/0.54    inference(avatar_component_clause,[],[f66])).
% 0.19/0.54  fof(f66,plain,(
% 0.19/0.54    spl3_5 <=> k1_xboole_0 = sK1),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.54  fof(f106,plain,(
% 0.19/0.54    ~r1_tarski(sK1,sK1) | spl3_10),
% 0.19/0.54    inference(avatar_component_clause,[],[f105])).
% 0.19/0.54  fof(f105,plain,(
% 0.19/0.54    spl3_10 <=> r1_tarski(sK1,sK1)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.54  fof(f172,plain,(
% 0.19/0.54    spl3_15 | ~spl3_5 | ~spl3_10),
% 0.19/0.54    inference(avatar_split_clause,[],[f161,f105,f66,f169])).
% 0.19/0.54  fof(f161,plain,(
% 0.19/0.54    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl3_5 | ~spl3_10)),
% 0.19/0.54    inference(backward_demodulation,[],[f142,f67])).
% 0.19/0.54  fof(f142,plain,(
% 0.19/0.54    k1_xboole_0 = k4_xboole_0(sK1,sK1) | ~spl3_10),
% 0.19/0.54    inference(resolution,[],[f107,f38])).
% 0.19/0.54  fof(f38,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f4])).
% 0.19/0.54  fof(f4,axiom,(
% 0.19/0.54    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.19/0.54  fof(f107,plain,(
% 0.19/0.54    r1_tarski(sK1,sK1) | ~spl3_10),
% 0.19/0.54    inference(avatar_component_clause,[],[f105])).
% 0.19/0.54  fof(f133,plain,(
% 0.19/0.54    spl3_12 | ~spl3_1 | ~spl3_5),
% 0.19/0.54    inference(avatar_split_clause,[],[f120,f66,f46,f130])).
% 0.19/0.54  fof(f120,plain,(
% 0.19/0.54    k4_xboole_0(k1_tarski(sK0),sK2) = k4_xboole_0(k1_xboole_0,sK2) | (~spl3_1 | ~spl3_5)),
% 0.19/0.54    inference(backward_demodulation,[],[f50,f67])).
% 0.19/0.54  fof(f50,plain,(
% 0.19/0.54    k4_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),sK2) | ~spl3_1),
% 0.19/0.54    inference(superposition,[],[f32,f48])).
% 0.19/0.54  fof(f32,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f6])).
% 0.19/0.54  fof(f6,axiom,(
% 0.19/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.19/0.54  fof(f118,plain,(
% 0.19/0.54    spl3_11 | ~spl3_1 | ~spl3_3),
% 0.19/0.54    inference(avatar_split_clause,[],[f100,f57,f46,f115])).
% 0.19/0.54  fof(f57,plain,(
% 0.19/0.54    spl3_3 <=> sK1 = k1_tarski(sK0)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.54  fof(f100,plain,(
% 0.19/0.54    sK1 = k2_xboole_0(sK1,sK2) | (~spl3_1 | ~spl3_3)),
% 0.19/0.54    inference(backward_demodulation,[],[f48,f58])).
% 0.19/0.54  fof(f58,plain,(
% 0.19/0.54    sK1 = k1_tarski(sK0) | ~spl3_3),
% 0.19/0.54    inference(avatar_component_clause,[],[f57])).
% 0.19/0.54  fof(f98,plain,(
% 0.19/0.54    spl3_9 | ~spl3_1 | spl3_3 | ~spl3_7),
% 0.19/0.54    inference(avatar_split_clause,[],[f83,f76,f57,f46,f95])).
% 0.19/0.54  fof(f76,plain,(
% 0.19/0.54    spl3_7 <=> r1_tarski(sK1,k1_tarski(sK0))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.54  fof(f83,plain,(
% 0.19/0.54    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) | (~spl3_1 | spl3_3 | ~spl3_7)),
% 0.19/0.54    inference(backward_demodulation,[],[f48,f82])).
% 0.19/0.54  fof(f82,plain,(
% 0.19/0.54    k1_xboole_0 = sK1 | (spl3_3 | ~spl3_7)),
% 0.19/0.54    inference(subsumption_resolution,[],[f80,f59])).
% 0.19/0.54  fof(f59,plain,(
% 0.19/0.54    sK1 != k1_tarski(sK0) | spl3_3),
% 0.19/0.54    inference(avatar_component_clause,[],[f57])).
% 0.19/0.54  fof(f80,plain,(
% 0.19/0.54    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1 | ~spl3_7),
% 0.19/0.54    inference(resolution,[],[f78,f35])).
% 0.19/0.54  fof(f78,plain,(
% 0.19/0.54    r1_tarski(sK1,k1_tarski(sK0)) | ~spl3_7),
% 0.19/0.54    inference(avatar_component_clause,[],[f76])).
% 0.19/0.54  fof(f93,plain,(
% 0.19/0.54    ~spl3_8 | spl3_3 | ~spl3_7),
% 0.19/0.54    inference(avatar_split_clause,[],[f85,f76,f57,f90])).
% 0.19/0.54  fof(f85,plain,(
% 0.19/0.54    k1_xboole_0 != k1_tarski(sK0) | (spl3_3 | ~spl3_7)),
% 0.19/0.54    inference(backward_demodulation,[],[f59,f82])).
% 0.19/0.54  fof(f88,plain,(
% 0.19/0.54    spl3_5 | spl3_3 | ~spl3_7),
% 0.19/0.54    inference(avatar_split_clause,[],[f82,f76,f57,f66])).
% 0.19/0.54  fof(f79,plain,(
% 0.19/0.54    spl3_7 | ~spl3_1),
% 0.19/0.54    inference(avatar_split_clause,[],[f51,f46,f76])).
% 0.19/0.54  fof(f51,plain,(
% 0.19/0.54    r1_tarski(sK1,k1_tarski(sK0)) | ~spl3_1),
% 0.19/0.54    inference(superposition,[],[f28,f48])).
% 0.19/0.54  fof(f74,plain,(
% 0.19/0.54    ~spl3_6 | ~spl3_3),
% 0.19/0.54    inference(avatar_split_clause,[],[f44,f57,f71])).
% 0.19/0.54  fof(f71,plain,(
% 0.19/0.54    spl3_6 <=> sK1 = sK2),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.54  fof(f44,plain,(
% 0.19/0.54    sK1 != k1_tarski(sK0) | sK1 != sK2),
% 0.19/0.54    inference(inner_rewriting,[],[f22])).
% 0.19/0.54  fof(f22,plain,(
% 0.19/0.54    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 0.19/0.54    inference(cnf_transformation,[],[f18])).
% 0.19/0.54  fof(f18,plain,(
% 0.19/0.54    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.19/0.54    inference(ennf_transformation,[],[f17])).
% 0.19/0.54  fof(f17,negated_conjecture,(
% 0.19/0.54    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.19/0.54    inference(negated_conjecture,[],[f16])).
% 0.19/0.54  fof(f16,conjecture,(
% 0.19/0.54    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.19/0.54  fof(f69,plain,(
% 0.19/0.54    ~spl3_4 | ~spl3_5),
% 0.19/0.54    inference(avatar_split_clause,[],[f21,f66,f62])).
% 0.19/0.54  fof(f21,plain,(
% 0.19/0.54    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 0.19/0.54    inference(cnf_transformation,[],[f18])).
% 0.19/0.54  fof(f60,plain,(
% 0.19/0.54    ~spl3_2 | ~spl3_3),
% 0.19/0.54    inference(avatar_split_clause,[],[f20,f57,f53])).
% 0.19/0.54  fof(f20,plain,(
% 0.19/0.54    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 0.19/0.54    inference(cnf_transformation,[],[f18])).
% 0.19/0.54  fof(f49,plain,(
% 0.19/0.54    spl3_1),
% 0.19/0.54    inference(avatar_split_clause,[],[f23,f46])).
% 0.19/0.54  fof(f23,plain,(
% 0.19/0.54    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.19/0.54    inference(cnf_transformation,[],[f18])).
% 0.19/0.54  % SZS output end Proof for theBenchmark
% 0.19/0.54  % (9395)------------------------------
% 0.19/0.54  % (9395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (9395)Termination reason: Refutation
% 0.19/0.54  
% 0.19/0.54  % (9395)Memory used [KB]: 10874
% 0.19/0.54  % (9395)Time elapsed: 0.131 s
% 0.19/0.54  % (9386)Refutation not found, incomplete strategy% (9386)------------------------------
% 0.19/0.54  % (9386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (9395)------------------------------
% 0.19/0.54  % (9395)------------------------------
% 0.19/0.54  % (9386)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (9386)Memory used [KB]: 10618
% 0.19/0.54  % (9386)Time elapsed: 0.141 s
% 0.19/0.54  % (9386)------------------------------
% 0.19/0.54  % (9386)------------------------------
% 0.19/0.54  % (9404)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.54  % (9374)Success in time 0.182 s
%------------------------------------------------------------------------------
