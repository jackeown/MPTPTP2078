%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 387 expanded)
%              Number of leaves         :   47 ( 180 expanded)
%              Depth                    :    7
%              Number of atoms          :  417 ( 793 expanded)
%              Number of equality atoms :  132 ( 305 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1399,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f57,f62,f69,f74,f81,f89,f99,f104,f116,f134,f156,f172,f226,f329,f349,f370,f436,f441,f476,f502,f527,f558,f573,f596,f655,f992,f1007,f1093,f1359,f1380,f1397,f1398])).

fof(f1398,plain,
    ( sK2 != k4_xboole_0(sK2,sK1)
    | r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1397,plain,
    ( spl3_62
    | ~ spl3_120 ),
    inference(avatar_split_clause,[],[f1386,f1377,f555])).

fof(f555,plain,
    ( spl3_62
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f1377,plain,
    ( spl3_120
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_120])])).

fof(f1386,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_120 ),
    inference(superposition,[],[f25,f1379])).

fof(f1379,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK0)
    | ~ spl3_120 ),
    inference(avatar_component_clause,[],[f1377])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1380,plain,
    ( spl3_120
    | ~ spl3_104
    | ~ spl3_118 ),
    inference(avatar_split_clause,[],[f1375,f1356,f1090,f1377])).

fof(f1090,plain,
    ( spl3_104
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_104])])).

fof(f1356,plain,
    ( spl3_118
  <=> sK2 = k4_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_118])])).

fof(f1375,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK0)
    | ~ spl3_104
    | ~ spl3_118 ),
    inference(forward_demodulation,[],[f1367,f1092])).

fof(f1092,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK2)
    | ~ spl3_104 ),
    inference(avatar_component_clause,[],[f1090])).

fof(f1367,plain,
    ( k3_xboole_0(sK2,sK0) = k4_xboole_0(sK2,sK2)
    | ~ spl3_118 ),
    inference(superposition,[],[f27,f1358])).

fof(f1358,plain,
    ( sK2 = k4_xboole_0(sK2,sK0)
    | ~ spl3_118 ),
    inference(avatar_component_clause,[],[f1356])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f1359,plain,
    ( spl3_118
    | ~ spl3_7
    | ~ spl3_95 ),
    inference(avatar_split_clause,[],[f1354,f1004,f71,f1356])).

fof(f71,plain,
    ( spl3_7
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f1004,plain,
    ( spl3_95
  <=> sK2 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_95])])).

fof(f1354,plain,
    ( sK2 = k4_xboole_0(sK2,sK0)
    | ~ spl3_7
    | ~ spl3_95 ),
    inference(forward_demodulation,[],[f1346,f1006])).

fof(f1006,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl3_95 ),
    inference(avatar_component_clause,[],[f1004])).

fof(f1346,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK0)
    | ~ spl3_7
    | ~ spl3_95 ),
    inference(superposition,[],[f1257,f73])).

fof(f73,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f1257,plain,
    ( ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k2_xboole_0(X0,sK1))
    | ~ spl3_95 ),
    inference(superposition,[],[f1073,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1073,plain,
    ( ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK2,X0)
    | ~ spl3_95 ),
    inference(superposition,[],[f35,f1006])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1093,plain,
    ( spl3_104
    | ~ spl3_4
    | ~ spl3_95 ),
    inference(avatar_split_clause,[],[f1088,f1004,f54,f1090])).

fof(f54,plain,
    ( spl3_4
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1088,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK2)
    | ~ spl3_4
    | ~ spl3_95 ),
    inference(forward_demodulation,[],[f1087,f56])).

fof(f56,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f1087,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK2)
    | ~ spl3_95 ),
    inference(forward_demodulation,[],[f1076,f25])).

fof(f1076,plain,
    ( k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2)
    | ~ spl3_95 ),
    inference(superposition,[],[f27,f1006])).

fof(f1007,plain,
    ( spl3_95
    | ~ spl3_12
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f1002,f520,f113,f1004])).

fof(f113,plain,
    ( spl3_12
  <=> sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f520,plain,
    ( spl3_57
  <=> r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f1002,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl3_12
    | ~ spl3_57 ),
    inference(forward_demodulation,[],[f996,f115])).

fof(f115,plain,
    ( sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f996,plain,
    ( k4_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1))
    | ~ spl3_57 ),
    inference(resolution,[],[f522,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f522,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK1))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f520])).

fof(f992,plain,
    ( spl3_58
    | ~ spl3_64
    | ~ spl3_71 ),
    inference(avatar_split_clause,[],[f991,f652,f593,f524])).

fof(f524,plain,
    ( spl3_58
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f593,plain,
    ( spl3_64
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f652,plain,
    ( spl3_71
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f991,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_64
    | ~ spl3_71 ),
    inference(forward_demodulation,[],[f984,f654])).

fof(f654,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl3_71 ),
    inference(avatar_component_clause,[],[f652])).

fof(f984,plain,
    ( k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK1,sK1)
    | ~ spl3_64
    | ~ spl3_71 ),
    inference(superposition,[],[f689,f926])).

fof(f926,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK2))
    | ~ spl3_64 ),
    inference(superposition,[],[f633,f26])).

fof(f633,plain,
    ( ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK1,X0)
    | ~ spl3_64 ),
    inference(superposition,[],[f35,f595])).

fof(f595,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f593])).

% (4387)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f689,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(sK1,X0))
    | ~ spl3_71 ),
    inference(superposition,[],[f35,f654])).

fof(f655,plain,
    ( spl3_71
    | ~ spl3_4
    | ~ spl3_64 ),
    inference(avatar_split_clause,[],[f650,f593,f54,f652])).

fof(f650,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl3_4
    | ~ spl3_64 ),
    inference(forward_demodulation,[],[f636,f56])).

fof(f636,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1)
    | ~ spl3_64 ),
    inference(superposition,[],[f27,f595])).

fof(f596,plain,
    ( spl3_64
    | ~ spl3_9
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f591,f495,f86,f593])).

fof(f86,plain,
    ( spl3_9
  <=> sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f495,plain,
    ( spl3_53
  <=> r1_tarski(k1_xboole_0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f591,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl3_9
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f585,f88])).

fof(f88,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f585,plain,
    ( k4_xboole_0(sK1,sK2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))
    | ~ spl3_53 ),
    inference(resolution,[],[f497,f29])).

fof(f497,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(sK1,sK2))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f495])).

fof(f573,plain,
    ( spl3_54
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f572,f353,f71,f66,f499])).

fof(f499,plain,
    ( spl3_54
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f66,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f353,plain,
    ( spl3_40
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f572,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_40 ),
    inference(forward_demodulation,[],[f560,f68])).

fof(f68,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f560,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_7
    | ~ spl3_40 ),
    inference(superposition,[],[f391,f73])).

fof(f391,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK0,X0))
    | ~ spl3_40 ),
    inference(superposition,[],[f35,f355])).

% (4377)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f355,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f353])).

fof(f558,plain,
    ( spl3_61
    | ~ spl3_62
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f548,f465,f555,f551])).

fof(f551,plain,
    ( spl3_61
  <=> r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f465,plain,
    ( spl3_52
  <=> k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)) = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f548,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    | ~ spl3_52 ),
    inference(superposition,[],[f32,f467])).

fof(f467,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)) = k3_xboole_0(sK0,sK2)
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f465])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

% (4378)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f527,plain,
    ( spl3_57
    | ~ spl3_58
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f515,f438,f524,f520])).

fof(f438,plain,
    ( spl3_48
  <=> k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) = k4_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f515,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK2)
    | r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK1))
    | ~ spl3_48 ),
    inference(superposition,[],[f33,f440])).

fof(f440,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) = k4_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f438])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f502,plain,
    ( spl3_53
    | ~ spl3_54
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f490,f433,f499,f495])).

fof(f433,plain,
    ( spl3_47
  <=> k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f490,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK1)
    | r1_tarski(k1_xboole_0,k4_xboole_0(sK1,sK2))
    | ~ spl3_47 ),
    inference(superposition,[],[f33,f435])).

fof(f435,plain,
    ( k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f433])).

fof(f476,plain,
    ( spl3_52
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f470,f153,f113,f465])).

fof(f153,plain,
    ( spl3_17
  <=> sK0 = k4_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f470,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)) = k3_xboole_0(sK0,sK2)
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(superposition,[],[f283,f115])).

fof(f283,plain,
    ( ! [X4] : k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X4)) = k3_xboole_0(sK0,X4)
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f270,f27])).

fof(f270,plain,
    ( ! [X4] : k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X4)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X4))
    | ~ spl3_17 ),
    inference(superposition,[],[f27,f157])).

fof(f157,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_17 ),
    inference(superposition,[],[f35,f155])).

fof(f155,plain,
    ( sK0 = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f153])).

fof(f441,plain,
    ( spl3_48
    | ~ spl3_12
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f425,f223,f113,f438])).

fof(f223,plain,
    ( spl3_26
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f425,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) = k4_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_12
    | ~ spl3_26 ),
    inference(superposition,[],[f228,f115])).

fof(f228,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0))
    | ~ spl3_26 ),
    inference(superposition,[],[f35,f225])).

fof(f225,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f223])).

fof(f436,plain,
    ( spl3_47
    | ~ spl3_9
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f424,f223,f86,f433])).

fof(f424,plain,
    ( k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))
    | ~ spl3_9
    | ~ spl3_26 ),
    inference(superposition,[],[f228,f88])).

fof(f370,plain,
    ( spl3_40
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f365,f200,f169,f353])).

fof(f169,plain,
    ( spl3_19
  <=> k4_xboole_0(sK0,sK0) = k3_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f200,plain,
    ( spl3_23
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f365,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_19
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f171,f201])).

fof(f201,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f200])).

fof(f171,plain,
    ( k4_xboole_0(sK0,sK0) = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f169])).

fof(f349,plain,
    ( spl3_23
    | ~ spl3_26
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f348,f326,f223,f200])).

fof(f326,plain,
    ( spl3_37
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f348,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_26
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f336,f225])).

fof(f336,plain,
    ( k3_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_37 ),
    inference(superposition,[],[f27,f328])).

fof(f328,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f326])).

fof(f329,plain,
    ( spl3_37
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f324,f71,f66,f326])).

fof(f324,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f317,f68])).

fof(f317,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(superposition,[],[f215,f73])).

fof(f215,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK1))
    | ~ spl3_6 ),
    inference(superposition,[],[f90,f26])).

fof(f90,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl3_6 ),
    inference(superposition,[],[f35,f68])).

fof(f226,plain,
    ( spl3_26
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f221,f66,f223])).

fof(f221,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f214,f68])).

fof(f214,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_6 ),
    inference(superposition,[],[f90,f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f172,plain,
    ( spl3_19
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f167,f153,f169])).

fof(f167,plain,
    ( k4_xboole_0(sK0,sK0) = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f160,f25])).

fof(f160,plain,
    ( k3_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK0)
    | ~ spl3_17 ),
    inference(superposition,[],[f27,f155])).

fof(f156,plain,
    ( spl3_17
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f151,f124,f101,f153])).

fof(f101,plain,
    ( spl3_11
  <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f124,plain,
    ( spl3_13
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f151,plain,
    ( sK0 = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f103,f126])).

fof(f126,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f124])).

fof(f103,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f134,plain,
    ( spl3_13
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f120,f96,f124])).

fof(f96,plain,
    ( spl3_10
  <=> sK0 = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f120,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_10 ),
    inference(superposition,[],[f24,f98])).

fof(f98,plain,
    ( sK0 = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f116,plain,
    ( spl3_12
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f108,f78,f113])).

fof(f78,plain,
    ( spl3_8
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f108,plain,
    ( sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1))
    | ~ spl3_8 ),
    inference(superposition,[],[f28,f80])).

fof(f80,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f104,plain,
    ( spl3_11
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f93,f66,f101])).

fof(f93,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_6 ),
    inference(superposition,[],[f27,f68])).

fof(f99,plain,
    ( spl3_10
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f92,f66,f96])).

fof(f92,plain,
    ( sK0 = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl3_6 ),
    inference(superposition,[],[f28,f68])).

fof(f89,plain,
    ( spl3_9
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f83,f54,f86])).

fof(f83,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))
    | ~ spl3_4 ),
    inference(superposition,[],[f28,f56])).

fof(f81,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f75,f59,f78])).

fof(f59,plain,
    ( spl3_5
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f75,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl3_5 ),
    inference(resolution,[],[f61,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f74,plain,
    ( spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f64,f47,f71])).

fof(f47,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f64,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f49,f29])).

fof(f49,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f69,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f63,f47,f66])).

fof(f63,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f52,f42,f59])).

fof(f42,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f52,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f44,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f44,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f57,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f51,f42,f54])).

fof(f51,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f44,f31])).

fof(f50,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f45,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f42])).

fof(f22,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f37])).

fof(f37,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f23,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:47:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.44  % (4385)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.46  % (4379)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (4385)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f1399,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f40,f45,f50,f57,f62,f69,f74,f81,f89,f99,f104,f116,f134,f156,f172,f226,f329,f349,f370,f436,f441,f476,f502,f527,f558,f573,f596,f655,f992,f1007,f1093,f1359,f1380,f1397,f1398])).
% 0.22/0.47  fof(f1398,plain,(
% 0.22/0.47    sK2 != k4_xboole_0(sK2,sK1) | r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 0.22/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.47  fof(f1397,plain,(
% 0.22/0.47    spl3_62 | ~spl3_120),
% 0.22/0.47    inference(avatar_split_clause,[],[f1386,f1377,f555])).
% 0.22/0.47  fof(f555,plain,(
% 0.22/0.47    spl3_62 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 0.22/0.47  fof(f1377,plain,(
% 0.22/0.47    spl3_120 <=> k1_xboole_0 = k3_xboole_0(sK2,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_120])])).
% 0.22/0.47  fof(f1386,plain,(
% 0.22/0.47    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_120),
% 0.22/0.47    inference(superposition,[],[f25,f1379])).
% 0.22/0.47  fof(f1379,plain,(
% 0.22/0.47    k1_xboole_0 = k3_xboole_0(sK2,sK0) | ~spl3_120),
% 0.22/0.47    inference(avatar_component_clause,[],[f1377])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.47  fof(f1380,plain,(
% 0.22/0.47    spl3_120 | ~spl3_104 | ~spl3_118),
% 0.22/0.47    inference(avatar_split_clause,[],[f1375,f1356,f1090,f1377])).
% 0.22/0.47  fof(f1090,plain,(
% 0.22/0.47    spl3_104 <=> k1_xboole_0 = k4_xboole_0(sK2,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_104])])).
% 0.22/0.47  fof(f1356,plain,(
% 0.22/0.47    spl3_118 <=> sK2 = k4_xboole_0(sK2,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_118])])).
% 0.22/0.47  fof(f1375,plain,(
% 0.22/0.47    k1_xboole_0 = k3_xboole_0(sK2,sK0) | (~spl3_104 | ~spl3_118)),
% 0.22/0.47    inference(forward_demodulation,[],[f1367,f1092])).
% 0.22/0.47  fof(f1092,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(sK2,sK2) | ~spl3_104),
% 0.22/0.47    inference(avatar_component_clause,[],[f1090])).
% 0.22/0.47  fof(f1367,plain,(
% 0.22/0.47    k3_xboole_0(sK2,sK0) = k4_xboole_0(sK2,sK2) | ~spl3_118),
% 0.22/0.47    inference(superposition,[],[f27,f1358])).
% 0.22/0.47  fof(f1358,plain,(
% 0.22/0.47    sK2 = k4_xboole_0(sK2,sK0) | ~spl3_118),
% 0.22/0.47    inference(avatar_component_clause,[],[f1356])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.47  fof(f1359,plain,(
% 0.22/0.47    spl3_118 | ~spl3_7 | ~spl3_95),
% 0.22/0.47    inference(avatar_split_clause,[],[f1354,f1004,f71,f1356])).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    spl3_7 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.47  fof(f1004,plain,(
% 0.22/0.47    spl3_95 <=> sK2 = k4_xboole_0(sK2,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_95])])).
% 0.22/0.47  fof(f1354,plain,(
% 0.22/0.47    sK2 = k4_xboole_0(sK2,sK0) | (~spl3_7 | ~spl3_95)),
% 0.22/0.47    inference(forward_demodulation,[],[f1346,f1006])).
% 0.22/0.47  fof(f1006,plain,(
% 0.22/0.47    sK2 = k4_xboole_0(sK2,sK1) | ~spl3_95),
% 0.22/0.47    inference(avatar_component_clause,[],[f1004])).
% 0.22/0.47  fof(f1346,plain,(
% 0.22/0.47    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK0) | (~spl3_7 | ~spl3_95)),
% 0.22/0.47    inference(superposition,[],[f1257,f73])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f71])).
% 0.22/0.47  fof(f1257,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k2_xboole_0(X0,sK1))) ) | ~spl3_95),
% 0.22/0.47    inference(superposition,[],[f1073,f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.47  fof(f1073,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK2,X0)) ) | ~spl3_95),
% 0.22/0.47    inference(superposition,[],[f35,f1006])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.47  fof(f1093,plain,(
% 0.22/0.47    spl3_104 | ~spl3_4 | ~spl3_95),
% 0.22/0.47    inference(avatar_split_clause,[],[f1088,f1004,f54,f1090])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    spl3_4 <=> k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.47  fof(f1088,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(sK2,sK2) | (~spl3_4 | ~spl3_95)),
% 0.22/0.47    inference(forward_demodulation,[],[f1087,f56])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl3_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f54])).
% 0.22/0.47  fof(f1087,plain,(
% 0.22/0.47    k3_xboole_0(sK1,sK2) = k4_xboole_0(sK2,sK2) | ~spl3_95),
% 0.22/0.47    inference(forward_demodulation,[],[f1076,f25])).
% 0.22/0.47  fof(f1076,plain,(
% 0.22/0.47    k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2) | ~spl3_95),
% 0.22/0.47    inference(superposition,[],[f27,f1006])).
% 0.22/0.47  fof(f1007,plain,(
% 0.22/0.47    spl3_95 | ~spl3_12 | ~spl3_57),
% 0.22/0.47    inference(avatar_split_clause,[],[f1002,f520,f113,f1004])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    spl3_12 <=> sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.47  fof(f520,plain,(
% 0.22/0.47    spl3_57 <=> r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.22/0.47  fof(f1002,plain,(
% 0.22/0.47    sK2 = k4_xboole_0(sK2,sK1) | (~spl3_12 | ~spl3_57)),
% 0.22/0.47    inference(forward_demodulation,[],[f996,f115])).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) | ~spl3_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f113])).
% 0.22/0.47  fof(f996,plain,(
% 0.22/0.47    k4_xboole_0(sK2,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) | ~spl3_57),
% 0.22/0.47    inference(resolution,[],[f522,f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.47  fof(f522,plain,(
% 0.22/0.47    r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK1)) | ~spl3_57),
% 0.22/0.47    inference(avatar_component_clause,[],[f520])).
% 0.22/0.47  fof(f992,plain,(
% 0.22/0.47    spl3_58 | ~spl3_64 | ~spl3_71),
% 0.22/0.47    inference(avatar_split_clause,[],[f991,f652,f593,f524])).
% 0.22/0.47  fof(f524,plain,(
% 0.22/0.47    spl3_58 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.22/0.47  fof(f593,plain,(
% 0.22/0.47    spl3_64 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.22/0.47  fof(f652,plain,(
% 0.22/0.47    spl3_71 <=> k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 0.22/0.47  fof(f991,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) | (~spl3_64 | ~spl3_71)),
% 0.22/0.47    inference(forward_demodulation,[],[f984,f654])).
% 0.22/0.47  fof(f654,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(sK1,sK1) | ~spl3_71),
% 0.22/0.47    inference(avatar_component_clause,[],[f652])).
% 0.22/0.47  fof(f984,plain,(
% 0.22/0.47    k4_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(sK1,sK1) | (~spl3_64 | ~spl3_71)),
% 0.22/0.47    inference(superposition,[],[f689,f926])).
% 0.22/0.47  fof(f926,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK2))) ) | ~spl3_64),
% 0.22/0.47    inference(superposition,[],[f633,f26])).
% 0.22/0.47  fof(f633,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK1,X0)) ) | ~spl3_64),
% 0.22/0.47    inference(superposition,[],[f35,f595])).
% 0.22/0.47  fof(f595,plain,(
% 0.22/0.47    sK1 = k4_xboole_0(sK1,sK2) | ~spl3_64),
% 0.22/0.47    inference(avatar_component_clause,[],[f593])).
% 0.22/0.47  % (4387)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  fof(f689,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(sK1,X0))) ) | ~spl3_71),
% 0.22/0.47    inference(superposition,[],[f35,f654])).
% 0.22/0.47  fof(f655,plain,(
% 0.22/0.47    spl3_71 | ~spl3_4 | ~spl3_64),
% 0.22/0.47    inference(avatar_split_clause,[],[f650,f593,f54,f652])).
% 0.22/0.47  fof(f650,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(sK1,sK1) | (~spl3_4 | ~spl3_64)),
% 0.22/0.47    inference(forward_demodulation,[],[f636,f56])).
% 0.22/0.47  fof(f636,plain,(
% 0.22/0.47    k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1) | ~spl3_64),
% 0.22/0.47    inference(superposition,[],[f27,f595])).
% 0.22/0.47  fof(f596,plain,(
% 0.22/0.47    spl3_64 | ~spl3_9 | ~spl3_53),
% 0.22/0.47    inference(avatar_split_clause,[],[f591,f495,f86,f593])).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    spl3_9 <=> sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.47  fof(f495,plain,(
% 0.22/0.47    spl3_53 <=> r1_tarski(k1_xboole_0,k4_xboole_0(sK1,sK2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.22/0.47  fof(f591,plain,(
% 0.22/0.47    sK1 = k4_xboole_0(sK1,sK2) | (~spl3_9 | ~spl3_53)),
% 0.22/0.47    inference(forward_demodulation,[],[f585,f88])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) | ~spl3_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f86])).
% 0.22/0.47  fof(f585,plain,(
% 0.22/0.47    k4_xboole_0(sK1,sK2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) | ~spl3_53),
% 0.22/0.47    inference(resolution,[],[f497,f29])).
% 0.22/0.47  fof(f497,plain,(
% 0.22/0.47    r1_tarski(k1_xboole_0,k4_xboole_0(sK1,sK2)) | ~spl3_53),
% 0.22/0.47    inference(avatar_component_clause,[],[f495])).
% 0.22/0.47  fof(f573,plain,(
% 0.22/0.47    spl3_54 | ~spl3_6 | ~spl3_7 | ~spl3_40),
% 0.22/0.47    inference(avatar_split_clause,[],[f572,f353,f71,f66,f499])).
% 0.22/0.47  fof(f499,plain,(
% 0.22/0.47    spl3_54 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.47  fof(f353,plain,(
% 0.22/0.47    spl3_40 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.22/0.47  fof(f572,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) | (~spl3_6 | ~spl3_7 | ~spl3_40)),
% 0.22/0.47    inference(forward_demodulation,[],[f560,f68])).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f66])).
% 0.22/0.47  fof(f560,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK1) = k4_xboole_0(k1_xboole_0,sK1) | (~spl3_7 | ~spl3_40)),
% 0.22/0.47    inference(superposition,[],[f391,f73])).
% 0.22/0.47  fof(f391,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK0,X0))) ) | ~spl3_40),
% 0.22/0.47    inference(superposition,[],[f35,f355])).
% 0.22/0.47  % (4377)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  fof(f355,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl3_40),
% 0.22/0.47    inference(avatar_component_clause,[],[f353])).
% 0.22/0.47  fof(f558,plain,(
% 0.22/0.47    spl3_61 | ~spl3_62 | ~spl3_52),
% 0.22/0.47    inference(avatar_split_clause,[],[f548,f465,f555,f551])).
% 0.22/0.47  fof(f551,plain,(
% 0.22/0.47    spl3_61 <=> r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.22/0.47  fof(f465,plain,(
% 0.22/0.47    spl3_52 <=> k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)) = k3_xboole_0(sK0,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.22/0.47  fof(f548,plain,(
% 0.22/0.47    k1_xboole_0 != k3_xboole_0(sK0,sK2) | r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) | ~spl3_52),
% 0.22/0.47    inference(superposition,[],[f32,f467])).
% 0.22/0.47  fof(f467,plain,(
% 0.22/0.47    k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)) = k3_xboole_0(sK0,sK2) | ~spl3_52),
% 0.22/0.47    inference(avatar_component_clause,[],[f465])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.47    inference(nnf_transformation,[],[f3])).
% 0.22/0.47  % (4378)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.47  fof(f527,plain,(
% 0.22/0.47    spl3_57 | ~spl3_58 | ~spl3_48),
% 0.22/0.47    inference(avatar_split_clause,[],[f515,f438,f524,f520])).
% 0.22/0.47  fof(f438,plain,(
% 0.22/0.47    spl3_48 <=> k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) = k4_xboole_0(k1_xboole_0,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.22/0.47  fof(f515,plain,(
% 0.22/0.47    k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK2) | r1_tarski(k1_xboole_0,k4_xboole_0(sK2,sK1)) | ~spl3_48),
% 0.22/0.47    inference(superposition,[],[f33,f440])).
% 0.22/0.47  fof(f440,plain,(
% 0.22/0.47    k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) = k4_xboole_0(k1_xboole_0,sK2) | ~spl3_48),
% 0.22/0.47    inference(avatar_component_clause,[],[f438])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.22/0.47    inference(nnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.47  fof(f502,plain,(
% 0.22/0.47    spl3_53 | ~spl3_54 | ~spl3_47),
% 0.22/0.47    inference(avatar_split_clause,[],[f490,f433,f499,f495])).
% 0.22/0.47  fof(f433,plain,(
% 0.22/0.47    spl3_47 <=> k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.22/0.47  fof(f490,plain,(
% 0.22/0.47    k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK1) | r1_tarski(k1_xboole_0,k4_xboole_0(sK1,sK2)) | ~spl3_47),
% 0.22/0.47    inference(superposition,[],[f33,f435])).
% 0.22/0.47  fof(f435,plain,(
% 0.22/0.47    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) | ~spl3_47),
% 0.22/0.47    inference(avatar_component_clause,[],[f433])).
% 0.22/0.47  fof(f476,plain,(
% 0.22/0.47    spl3_52 | ~spl3_12 | ~spl3_17),
% 0.22/0.47    inference(avatar_split_clause,[],[f470,f153,f113,f465])).
% 0.22/0.47  fof(f153,plain,(
% 0.22/0.47    spl3_17 <=> sK0 = k4_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.47  fof(f470,plain,(
% 0.22/0.47    k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)) = k3_xboole_0(sK0,sK2) | (~spl3_12 | ~spl3_17)),
% 0.22/0.47    inference(superposition,[],[f283,f115])).
% 0.22/0.47  fof(f283,plain,(
% 0.22/0.47    ( ! [X4] : (k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X4)) = k3_xboole_0(sK0,X4)) ) | ~spl3_17),
% 0.22/0.47    inference(forward_demodulation,[],[f270,f27])).
% 0.22/0.47  fof(f270,plain,(
% 0.22/0.47    ( ! [X4] : (k3_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X4)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X4))) ) | ~spl3_17),
% 0.22/0.47    inference(superposition,[],[f27,f157])).
% 0.22/0.47  fof(f157,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(sK0,X0)) ) | ~spl3_17),
% 0.22/0.47    inference(superposition,[],[f35,f155])).
% 0.22/0.47  fof(f155,plain,(
% 0.22/0.47    sK0 = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_17),
% 0.22/0.47    inference(avatar_component_clause,[],[f153])).
% 0.22/0.47  fof(f441,plain,(
% 0.22/0.47    spl3_48 | ~spl3_12 | ~spl3_26),
% 0.22/0.47    inference(avatar_split_clause,[],[f425,f223,f113,f438])).
% 0.22/0.47  fof(f223,plain,(
% 0.22/0.47    spl3_26 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.47  fof(f425,plain,(
% 0.22/0.47    k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) = k4_xboole_0(k1_xboole_0,sK2) | (~spl3_12 | ~spl3_26)),
% 0.22/0.47    inference(superposition,[],[f228,f115])).
% 0.22/0.47  fof(f228,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0))) ) | ~spl3_26),
% 0.22/0.47    inference(superposition,[],[f35,f225])).
% 0.22/0.47  fof(f225,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_26),
% 0.22/0.47    inference(avatar_component_clause,[],[f223])).
% 0.22/0.47  fof(f436,plain,(
% 0.22/0.47    spl3_47 | ~spl3_9 | ~spl3_26),
% 0.22/0.47    inference(avatar_split_clause,[],[f424,f223,f86,f433])).
% 0.22/0.47  fof(f424,plain,(
% 0.22/0.47    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) | (~spl3_9 | ~spl3_26)),
% 0.22/0.47    inference(superposition,[],[f228,f88])).
% 0.22/0.47  fof(f370,plain,(
% 0.22/0.47    spl3_40 | ~spl3_19 | ~spl3_23),
% 0.22/0.47    inference(avatar_split_clause,[],[f365,f200,f169,f353])).
% 0.22/0.47  fof(f169,plain,(
% 0.22/0.47    spl3_19 <=> k4_xboole_0(sK0,sK0) = k3_xboole_0(k1_xboole_0,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.47  fof(f200,plain,(
% 0.22/0.47    spl3_23 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.47  fof(f365,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK0) | (~spl3_19 | ~spl3_23)),
% 0.22/0.47    inference(backward_demodulation,[],[f171,f201])).
% 0.22/0.47  fof(f201,plain,(
% 0.22/0.47    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) | ~spl3_23),
% 0.22/0.47    inference(avatar_component_clause,[],[f200])).
% 0.22/0.47  fof(f171,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK0) = k3_xboole_0(k1_xboole_0,sK0) | ~spl3_19),
% 0.22/0.47    inference(avatar_component_clause,[],[f169])).
% 0.22/0.47  fof(f349,plain,(
% 0.22/0.47    spl3_23 | ~spl3_26 | ~spl3_37),
% 0.22/0.47    inference(avatar_split_clause,[],[f348,f326,f223,f200])).
% 0.22/0.47  fof(f326,plain,(
% 0.22/0.47    spl3_37 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.22/0.47  fof(f348,plain,(
% 0.22/0.47    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) | (~spl3_26 | ~spl3_37)),
% 0.22/0.47    inference(forward_demodulation,[],[f336,f225])).
% 0.22/0.47  fof(f336,plain,(
% 0.22/0.47    k3_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_37),
% 0.22/0.47    inference(superposition,[],[f27,f328])).
% 0.22/0.47  fof(f328,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) | ~spl3_37),
% 0.22/0.47    inference(avatar_component_clause,[],[f326])).
% 0.22/0.47  fof(f329,plain,(
% 0.22/0.47    spl3_37 | ~spl3_6 | ~spl3_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f324,f71,f66,f326])).
% 0.22/0.47  fof(f324,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) | (~spl3_6 | ~spl3_7)),
% 0.22/0.47    inference(forward_demodulation,[],[f317,f68])).
% 0.22/0.47  fof(f317,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK1) = k4_xboole_0(k1_xboole_0,sK0) | (~spl3_6 | ~spl3_7)),
% 0.22/0.47    inference(superposition,[],[f215,f73])).
% 0.22/0.47  fof(f215,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,sK1))) ) | ~spl3_6),
% 0.22/0.47    inference(superposition,[],[f90,f26])).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl3_6),
% 0.22/0.47    inference(superposition,[],[f35,f68])).
% 0.22/0.47  fof(f226,plain,(
% 0.22/0.47    spl3_26 | ~spl3_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f221,f66,f223])).
% 0.22/0.47  fof(f221,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_6),
% 0.22/0.47    inference(forward_demodulation,[],[f214,f68])).
% 0.22/0.47  fof(f214,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK1) = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_6),
% 0.22/0.47    inference(superposition,[],[f90,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.47  fof(f172,plain,(
% 0.22/0.47    spl3_19 | ~spl3_17),
% 0.22/0.47    inference(avatar_split_clause,[],[f167,f153,f169])).
% 0.22/0.47  fof(f167,plain,(
% 0.22/0.47    k4_xboole_0(sK0,sK0) = k3_xboole_0(k1_xboole_0,sK0) | ~spl3_17),
% 0.22/0.47    inference(forward_demodulation,[],[f160,f25])).
% 0.22/0.47  fof(f160,plain,(
% 0.22/0.47    k3_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK0) | ~spl3_17),
% 0.22/0.47    inference(superposition,[],[f27,f155])).
% 0.22/0.47  fof(f156,plain,(
% 0.22/0.47    spl3_17 | ~spl3_11 | ~spl3_13),
% 0.22/0.47    inference(avatar_split_clause,[],[f151,f124,f101,f153])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    spl3_11 <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.47  fof(f124,plain,(
% 0.22/0.47    spl3_13 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.47  fof(f151,plain,(
% 0.22/0.47    sK0 = k4_xboole_0(sK0,k1_xboole_0) | (~spl3_11 | ~spl3_13)),
% 0.22/0.47    inference(forward_demodulation,[],[f103,f126])).
% 0.22/0.47  fof(f126,plain,(
% 0.22/0.47    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_13),
% 0.22/0.47    inference(avatar_component_clause,[],[f124])).
% 0.22/0.47  fof(f103,plain,(
% 0.22/0.47    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f101])).
% 0.22/0.47  fof(f134,plain,(
% 0.22/0.47    spl3_13 | ~spl3_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f120,f96,f124])).
% 0.22/0.47  fof(f96,plain,(
% 0.22/0.47    spl3_10 <=> sK0 = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.47  fof(f120,plain,(
% 0.22/0.47    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_10),
% 0.22/0.47    inference(superposition,[],[f24,f98])).
% 0.22/0.47  fof(f98,plain,(
% 0.22/0.47    sK0 = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) | ~spl3_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f96])).
% 0.22/0.47  fof(f116,plain,(
% 0.22/0.47    spl3_12 | ~spl3_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f108,f78,f113])).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    spl3_8 <=> k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) | ~spl3_8),
% 0.22/0.47    inference(superposition,[],[f28,f80])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl3_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f78])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.47  fof(f104,plain,(
% 0.22/0.47    spl3_11 | ~spl3_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f93,f66,f101])).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_6),
% 0.22/0.47    inference(superposition,[],[f27,f68])).
% 0.22/0.47  fof(f99,plain,(
% 0.22/0.47    spl3_10 | ~spl3_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f92,f66,f96])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    sK0 = k2_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) | ~spl3_6),
% 0.22/0.47    inference(superposition,[],[f28,f68])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    spl3_9 | ~spl3_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f83,f54,f86])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) | ~spl3_4),
% 0.22/0.47    inference(superposition,[],[f28,f56])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    spl3_8 | ~spl3_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f75,f59,f78])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    spl3_5 <=> r1_xboole_0(sK2,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl3_5),
% 0.22/0.47    inference(resolution,[],[f61,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    r1_xboole_0(sK2,sK1) | ~spl3_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f59])).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    spl3_7 | ~spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f64,f47,f71])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.47    inference(resolution,[],[f49,f29])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f47])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    spl3_6 | ~spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f63,f47,f66])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.47    inference(resolution,[],[f49,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    spl3_5 | ~spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f52,f42,f59])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    spl3_2 <=> r1_xboole_0(sK1,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    r1_xboole_0(sK2,sK1) | ~spl3_2),
% 0.22/0.47    inference(resolution,[],[f44,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    r1_xboole_0(sK1,sK2) | ~spl3_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f42])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    spl3_4 | ~spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f51,f42,f54])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl3_2),
% 0.22/0.47    inference(resolution,[],[f44,f31])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f21,f47])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    r1_tarski(sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.47    inference(negated_conjecture,[],[f11])).
% 0.22/0.47  fof(f11,conjecture,(
% 0.22/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f22,f42])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    r1_xboole_0(sK1,sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ~spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f23,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    spl3_1 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ~r1_xboole_0(sK0,sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (4385)------------------------------
% 0.22/0.47  % (4385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (4385)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (4385)Memory used [KB]: 11385
% 0.22/0.47  % (4385)Time elapsed: 0.032 s
% 0.22/0.47  % (4385)------------------------------
% 0.22/0.47  % (4385)------------------------------
% 0.22/0.47  % (4391)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.47  % (4369)Success in time 0.113 s
%------------------------------------------------------------------------------
