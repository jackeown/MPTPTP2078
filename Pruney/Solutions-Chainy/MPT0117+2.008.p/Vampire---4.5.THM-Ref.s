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
% DateTime   : Thu Dec  3 12:32:52 EST 2020

% Result     : Theorem 33.24s
% Output     : Refutation 33.24s
% Verified   : 
% Statistics : Number of formulae       :  427 (10145 expanded)
%              Number of leaves         :   72 (3320 expanded)
%              Depth                    :   44
%              Number of atoms          :  879 (12947 expanded)
%              Number of equality atoms :  301 (8974 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115390,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f69,f74,f87,f92,f97,f102,f107,f159,f164,f178,f293,f351,f389,f428,f528,f539,f544,f564,f602,f616,f5816,f5822,f6055,f6060,f13484,f13513,f13540,f19201,f19224,f26043,f26093,f26138,f26189,f30515,f31575,f31580,f44177,f44450,f44456,f44576,f44722,f50822,f64359,f64453,f64699,f78529,f78658,f98249,f98512,f98680,f113818,f113956,f114739,f115336,f115360,f115364])).

fof(f115364,plain,
    ( spl3_3
    | ~ spl3_5
    | ~ spl3_23
    | ~ spl3_56 ),
    inference(avatar_contradiction_clause,[],[f115363])).

fof(f115363,plain,
    ( $false
    | spl3_3
    | ~ spl3_5
    | ~ spl3_23
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f115362,f52])).

fof(f52,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_3
  <=> r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f115362,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    | ~ spl3_5
    | ~ spl3_23
    | ~ spl3_56 ),
    inference(forward_demodulation,[],[f115292,f615])).

fof(f615,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f613])).

fof(f613,plain,
    ( spl3_23
  <=> sK1 = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f115292,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK2),k2_xboole_0(sK2,sK1))
    | ~ spl3_5
    | ~ spl3_56 ),
    inference(superposition,[],[f61688,f114738])).

fof(f114738,plain,
    ( k5_xboole_0(sK0,sK2) = k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f114736])).

fof(f114736,plain,
    ( spl3_56
  <=> k5_xboole_0(sK0,sK2) = k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f61688,plain,
    ( ! [X17,X18] : r1_tarski(k3_xboole_0(X18,X17),k2_xboole_0(sK2,X17))
    | ~ spl3_5 ),
    inference(superposition,[],[f1104,f61508])).

fof(f61508,plain,
    ( ! [X1] : k2_xboole_0(sK2,X1) = k2_xboole_0(X1,sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f60855,f271])).

fof(f271,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f224,f173])).

fof(f173,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f31,f151])).

fof(f151,plain,(
    ! [X7] : k4_xboole_0(X7,k1_xboole_0) = X7 ),
    inference(forward_demodulation,[],[f144,f27])).

fof(f27,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f144,plain,(
    ! [X7] : k4_xboole_0(X7,k1_xboole_0) = k5_xboole_0(X7,k1_xboole_0) ),
    inference(superposition,[],[f32,f114])).

fof(f114,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f62,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f62,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3) ),
    inference(resolution,[],[f34,f25])).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f224,plain,(
    ! [X7] : k2_xboole_0(k1_xboole_0,X7) = X7 ),
    inference(forward_demodulation,[],[f208,f151])).

fof(f208,plain,(
    ! [X7] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X7,k1_xboole_0)) = X7 ),
    inference(superposition,[],[f33,f114])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f60855,plain,
    ( ! [X2] : k2_xboole_0(X2,sK2) = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK2,X2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f60819,f27])).

fof(f60819,plain,
    ( ! [X2] : k5_xboole_0(k1_xboole_0,k2_xboole_0(sK2,X2)) = k5_xboole_0(k2_xboole_0(X2,sK2),k1_xboole_0)
    | ~ spl3_5 ),
    inference(superposition,[],[f255,f60338])).

fof(f60338,plain,
    ( ! [X4] : k1_xboole_0 = k5_xboole_0(k2_xboole_0(X4,sK2),k2_xboole_0(sK2,X4))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f60316,f31])).

fof(f60316,plain,
    ( ! [X4] : k1_xboole_0 = k5_xboole_0(k2_xboole_0(X4,sK2),k5_xboole_0(sK2,k4_xboole_0(X4,sK2)))
    | ~ spl3_5 ),
    inference(superposition,[],[f261,f60283])).

fof(f60283,plain,
    ( ! [X0] : k4_xboole_0(X0,sK2) = k5_xboole_0(k2_xboole_0(X0,sK2),sK2)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f60250,f141])).

fof(f141,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f32,f29])).

fof(f60250,plain,
    ( ! [X0] : k5_xboole_0(k2_xboole_0(X0,sK2),sK2) = k5_xboole_0(X0,k3_xboole_0(sK2,X0))
    | ~ spl3_5 ),
    inference(superposition,[],[f257,f59894])).

fof(f59894,plain,
    ( ! [X20] : k3_xboole_0(sK2,X20) = k5_xboole_0(k4_xboole_0(sK2,X20),sK2)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f59759,f33573])).

fof(f33573,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f33572,f271])).

fof(f33572,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f33571,f642])).

fof(f642,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X7,X6)) = X6 ),
    inference(forward_demodulation,[],[f632,f27])).

fof(f632,plain,(
    ! [X6,X7] : k5_xboole_0(X6,k1_xboole_0) = k4_xboole_0(X6,k4_xboole_0(X7,X6)) ),
    inference(superposition,[],[f32,f575])).

fof(f575,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f36,f219])).

fof(f219,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f150,f33])).

fof(f150,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f143,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f143,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(X5,X5) ),
    inference(superposition,[],[f32,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(resolution,[],[f34,f28])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f33571,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f33570,f271])).

fof(f33570,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)))) ),
    inference(forward_demodulation,[],[f33569,f173])).

fof(f33569,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)))) ),
    inference(forward_demodulation,[],[f33382,f224])).

fof(f33382,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))))) ),
    inference(superposition,[],[f1537,f152])).

fof(f152,plain,(
    ! [X8] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X8) ),
    inference(forward_demodulation,[],[f145,f26])).

fof(f145,plain,(
    ! [X8] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X8) ),
    inference(superposition,[],[f32,f62])).

fof(f1537,plain,(
    ! [X14,X12,X13] : k4_xboole_0(k5_xboole_0(X14,k3_xboole_0(X12,X13)),k4_xboole_0(X12,X13)) = k2_xboole_0(k4_xboole_0(X14,X12),k3_xboole_0(X12,k4_xboole_0(X13,k2_xboole_0(X14,k4_xboole_0(X12,X13))))) ),
    inference(forward_demodulation,[],[f1478,f36])).

fof(f1478,plain,(
    ! [X14,X12,X13] : k4_xboole_0(k5_xboole_0(X14,k3_xboole_0(X12,X13)),k4_xboole_0(X12,X13)) = k2_xboole_0(k4_xboole_0(X14,X12),k4_xboole_0(k3_xboole_0(X12,X13),k2_xboole_0(X14,k4_xboole_0(X12,X13)))) ),
    inference(superposition,[],[f38,f33])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).

fof(f59759,plain,
    ( ! [X20] : k4_xboole_0(k3_xboole_0(sK2,X20),k4_xboole_0(sK2,X20)) = k5_xboole_0(k4_xboole_0(sK2,X20),sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f409,f893])).

fof(f893,plain,
    ( ! [X4] : sK2 = k2_xboole_0(k4_xboole_0(sK2,X4),k3_xboole_0(sK2,X4))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f876,f892])).

fof(f892,plain,
    ( ! [X3] : k4_xboole_0(sK2,k4_xboole_0(sK1,X3)) = k3_xboole_0(sK2,X3)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f875,f407])).

fof(f407,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f394,f271])).

fof(f394,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f255,f32])).

fof(f875,plain,
    ( ! [X3] : k4_xboole_0(sK2,k4_xboole_0(sK1,X3)) = k5_xboole_0(sK2,k4_xboole_0(sK2,X3))
    | ~ spl3_5 ),
    inference(superposition,[],[f32,f574])).

fof(f574,plain,
    ( ! [X18] : k3_xboole_0(sK2,k4_xboole_0(sK1,X18)) = k4_xboole_0(sK2,X18)
    | ~ spl3_5 ),
    inference(superposition,[],[f36,f73])).

fof(f73,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_5
  <=> sK2 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f876,plain,
    ( ! [X4] : sK2 = k2_xboole_0(k4_xboole_0(sK2,X4),k4_xboole_0(sK2,k4_xboole_0(sK1,X4)))
    | ~ spl3_5 ),
    inference(superposition,[],[f33,f574])).

fof(f409,plain,(
    ! [X6,X5] : k4_xboole_0(X6,X5) = k5_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f396,f271])).

fof(f396,plain,(
    ! [X6,X5] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X6,X5)) = k5_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f255,f31])).

fof(f257,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(k4_xboole_0(X6,X5),X7)) = k5_xboole_0(k2_xboole_0(X5,X6),X7) ),
    inference(superposition,[],[f35,f31])).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f261,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f35,f26])).

fof(f255,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f35,f26])).

fof(f1104,plain,(
    ! [X12,X13,X11] : r1_tarski(k3_xboole_0(X13,X11),k2_xboole_0(X11,X12)) ),
    inference(superposition,[],[f991,f60])).

fof(f991,plain,(
    ! [X37,X38,X36] : r1_tarski(k3_xboole_0(X36,k3_xboole_0(X37,X38)),X38) ),
    inference(superposition,[],[f237,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f237,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f221,f29])).

fof(f221,plain,(
    ! [X4,X5] : r1_tarski(k3_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f28,f33])).

fof(f115360,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_21
    | ~ spl3_56 ),
    inference(avatar_contradiction_clause,[],[f115359])).

fof(f115359,plain,
    ( $false
    | spl3_3
    | ~ spl3_4
    | ~ spl3_21
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f115358,f52])).

fof(f115358,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    | ~ spl3_4
    | ~ spl3_21
    | ~ spl3_56 ),
    inference(forward_demodulation,[],[f115288,f563])).

fof(f563,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl3_21
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f115288,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK2),k2_xboole_0(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_56 ),
    inference(superposition,[],[f41612,f114738])).

fof(f41612,plain,
    ( ! [X19,X20] : r1_tarski(k3_xboole_0(X20,X19),k2_xboole_0(sK0,X19))
    | ~ spl3_4 ),
    inference(superposition,[],[f1104,f41509])).

fof(f41509,plain,
    ( ! [X1] : k2_xboole_0(sK0,X1) = k2_xboole_0(X1,sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f40236,f271])).

fof(f40236,plain,
    ( ! [X2] : k2_xboole_0(X2,sK0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X2))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f40204,f27])).

fof(f40204,plain,
    ( ! [X2] : k5_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X2)) = k5_xboole_0(k2_xboole_0(X2,sK0),k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f255,f38146])).

fof(f38146,plain,
    ( ! [X4] : k1_xboole_0 = k5_xboole_0(k2_xboole_0(X4,sK0),k2_xboole_0(sK0,X4))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f38126,f31])).

fof(f38126,plain,
    ( ! [X4] : k1_xboole_0 = k5_xboole_0(k2_xboole_0(X4,sK0),k5_xboole_0(sK0,k4_xboole_0(X4,sK0)))
    | ~ spl3_4 ),
    inference(superposition,[],[f261,f34928])).

fof(f34928,plain,
    ( ! [X1] : k4_xboole_0(X1,sK0) = k5_xboole_0(k2_xboole_0(X1,sK0),sK0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f34891,f141])).

fof(f34891,plain,
    ( ! [X1] : k5_xboole_0(k2_xboole_0(X1,sK0),sK0) = k5_xboole_0(X1,k3_xboole_0(sK0,X1))
    | ~ spl3_4 ),
    inference(superposition,[],[f257,f29637])).

fof(f29637,plain,
    ( ! [X10] : k3_xboole_0(sK0,X10) = k5_xboole_0(k4_xboole_0(sK0,X10),sK0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f29599,f719])).

fof(f719,plain,
    ( ! [X3] : k4_xboole_0(sK0,k4_xboole_0(sK1,X3)) = k3_xboole_0(sK0,X3)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f703,f407])).

fof(f703,plain,
    ( ! [X3] : k4_xboole_0(sK0,k4_xboole_0(sK1,X3)) = k5_xboole_0(sK0,k4_xboole_0(sK0,X3))
    | ~ spl3_4 ),
    inference(superposition,[],[f32,f571])).

fof(f571,plain,
    ( ! [X15] : k3_xboole_0(sK0,k4_xboole_0(sK1,X15)) = k4_xboole_0(sK0,X15)
    | ~ spl3_4 ),
    inference(superposition,[],[f36,f68])).

fof(f68,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_4
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f29599,plain,
    ( ! [X10] : k4_xboole_0(sK0,k4_xboole_0(sK1,X10)) = k5_xboole_0(k4_xboole_0(sK0,X10),sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f21880,f571])).

fof(f21880,plain,
    ( ! [X3] : k4_xboole_0(sK0,X3) = k5_xboole_0(k3_xboole_0(sK0,X3),sK0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f21827,f271])).

fof(f21827,plain,
    ( ! [X3] : k5_xboole_0(k3_xboole_0(sK0,X3),sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X3))
    | ~ spl3_4 ),
    inference(superposition,[],[f255,f15322])).

fof(f15322,plain,
    ( ! [X44] : sK0 = k5_xboole_0(k3_xboole_0(sK0,X44),k4_xboole_0(sK0,X44))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f15279,f8723])).

fof(f8723,plain,
    ( ! [X3] : sK0 = k2_xboole_0(k3_xboole_0(sK0,X3),sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f8713,f719])).

fof(f8713,plain,
    ( ! [X31] : sK0 = k2_xboole_0(k4_xboole_0(sK0,X31),sK0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f8681,f6382])).

fof(f6382,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f6299,f27])).

fof(f6299,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f256,f26])).

fof(f256,plain,(
    ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X3),X4)) = k5_xboole_0(k4_xboole_0(X2,X3),X4) ),
    inference(superposition,[],[f35,f32])).

fof(f8681,plain,
    ( ! [X31] : k2_xboole_0(k4_xboole_0(sK0,X31),sK0) = k5_xboole_0(k4_xboole_0(sK0,X31),k3_xboole_0(sK0,X31))
    | ~ spl3_4 ),
    inference(superposition,[],[f31,f3510])).

fof(f3510,plain,
    ( ! [X21] : k3_xboole_0(sK0,X21) = k4_xboole_0(sK0,k4_xboole_0(sK0,X21))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f3491,f407])).

fof(f3491,plain,
    ( ! [X21] : k4_xboole_0(sK0,k4_xboole_0(sK0,X21)) = k5_xboole_0(sK0,k4_xboole_0(sK0,X21))
    | ~ spl3_4 ),
    inference(superposition,[],[f141,f721])).

fof(f721,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k3_xboole_0(k4_xboole_0(sK0,X0),sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f710,f34])).

fof(f710,plain,
    ( ! [X11] : r1_tarski(k4_xboole_0(sK0,X11),sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f221,f571])).

fof(f15279,plain,
    ( ! [X44] : k2_xboole_0(k3_xboole_0(sK0,X44),sK0) = k5_xboole_0(k3_xboole_0(sK0,X44),k4_xboole_0(sK0,X44))
    | ~ spl3_4 ),
    inference(superposition,[],[f31,f8693])).

fof(f8693,plain,
    ( ! [X3] : k4_xboole_0(sK0,X3) = k4_xboole_0(sK0,k3_xboole_0(sK0,X3))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f8647,f571])).

fof(f8647,plain,
    ( ! [X3] : k3_xboole_0(sK0,k4_xboole_0(sK1,X3)) = k4_xboole_0(sK0,k3_xboole_0(sK0,X3))
    | ~ spl3_4 ),
    inference(superposition,[],[f3510,f719])).

fof(f115336,plain,
    ( spl3_3
    | ~ spl3_56 ),
    inference(avatar_contradiction_clause,[],[f115335])).

fof(f115335,plain,
    ( $false
    | spl3_3
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f115250,f52])).

fof(f115250,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    | ~ spl3_56 ),
    inference(superposition,[],[f237,f114738])).

fof(f114739,plain,
    ( spl3_56
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f98645,f98509,f114736])).

fof(f98509,plain,
    ( spl3_52
  <=> k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f98645,plain,
    ( k5_xboole_0(sK0,sK2) = k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f98572,f27])).

fof(f98572,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) = k5_xboole_0(k5_xboole_0(sK0,sK2),k1_xboole_0)
    | ~ spl3_52 ),
    inference(superposition,[],[f407,f98511])).

fof(f98511,plain,
    ( k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK2),sK1)
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f98509])).

fof(f113956,plain,
    ( spl3_55
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f113928,f113815,f113953])).

fof(f113953,plain,
    ( spl3_55
  <=> sK1 = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f113815,plain,
    ( spl3_54
  <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f113928,plain,
    ( sK1 = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f113869,f27])).

fof(f113869,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | ~ spl3_54 ),
    inference(superposition,[],[f31,f113817])).

fof(f113817,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f113815])).

fof(f113818,plain,
    ( spl3_54
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f98169,f613,f425,f66,f113815])).

fof(f425,plain,
    ( spl3_17
  <=> sK0 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f98169,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f98066,f41509])).

fof(f98066,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK2,sK0),sK1)
    | ~ spl3_17
    | ~ spl3_23 ),
    inference(superposition,[],[f83908,f427])).

fof(f427,plain,
    ( sK0 = k3_xboole_0(sK1,sK0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f425])).

fof(f83908,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK2,k3_xboole_0(sK1,X0)),sK1)
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f83874,f114])).

fof(f83874,plain,
    ( ! [X0] : k4_xboole_0(k2_xboole_0(sK2,k3_xboole_0(sK1,X0)),sK1) = k3_xboole_0(k4_xboole_0(k2_xboole_0(sK2,k3_xboole_0(sK1,X0)),sK1),k1_xboole_0)
    | ~ spl3_23 ),
    inference(resolution,[],[f75919,f34])).

fof(f75919,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(k2_xboole_0(sK2,k3_xboole_0(sK1,X0)),sK1),k1_xboole_0)
    | ~ spl3_23 ),
    inference(superposition,[],[f71804,f585])).

fof(f585,plain,(
    ! [X14,X12,X13] : k2_xboole_0(X14,k3_xboole_0(X12,X13)) = k5_xboole_0(X14,k3_xboole_0(X12,k4_xboole_0(X13,X14))) ),
    inference(superposition,[],[f31,f36])).

fof(f71804,plain,
    ( ! [X14] : r1_tarski(k4_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK1,X14)),sK1),k1_xboole_0)
    | ~ spl3_23 ),
    inference(superposition,[],[f65838,f219])).

fof(f65838,plain,
    ( ! [X70] : r1_tarski(k4_xboole_0(k5_xboole_0(sK2,X70),sK1),k4_xboole_0(X70,sK1))
    | ~ spl3_23 ),
    inference(superposition,[],[f5548,f65556])).

fof(f65556,plain,(
    ! [X14,X15] : k5_xboole_0(k5_xboole_0(X15,X14),X15) = X14 ),
    inference(superposition,[],[f62139,f62139])).

fof(f62139,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,X2)) = X3 ),
    inference(superposition,[],[f515,f271])).

fof(f515,plain,(
    ! [X2,X3] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k5_xboole_0(X2,X3))) = X2 ),
    inference(forward_demodulation,[],[f489,f27])).

fof(f489,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k5_xboole_0(X2,X3))) ),
    inference(superposition,[],[f255,f261])).

fof(f5548,plain,
    ( ! [X59] : r1_tarski(k4_xboole_0(X59,sK1),k4_xboole_0(k5_xboole_0(X59,sK2),sK1))
    | ~ spl3_23 ),
    inference(superposition,[],[f1531,f615])).

fof(f1531,plain,(
    ! [X10,X8,X9] : r1_tarski(k4_xboole_0(X8,k2_xboole_0(X9,X10)),k4_xboole_0(k5_xboole_0(X8,X9),X10)) ),
    inference(superposition,[],[f28,f38])).

fof(f98680,plain,
    ( spl3_53
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f98642,f98509,f98677])).

fof(f98677,plain,
    ( spl3_53
  <=> sK1 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f98642,plain,
    ( sK1 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK2))
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f98568,f27])).

fof(f98568,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k5_xboole_0(sK0,sK2))
    | ~ spl3_52 ),
    inference(superposition,[],[f31,f98511])).

fof(f98512,plain,
    ( spl3_52
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f84062,f613,f425,f66,f98509])).

fof(f84062,plain,
    ( k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK2),sK1)
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f83960,f58842])).

fof(f58842,plain,
    ( ! [X6] : k5_xboole_0(sK0,X6) = k5_xboole_0(X6,sK0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f58816,f271])).

fof(f58816,plain,
    ( ! [X6] : k5_xboole_0(sK0,X6) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X6),sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f58723,f255])).

fof(f58723,plain,
    ( ! [X3] : k5_xboole_0(k5_xboole_0(sK0,X3),sK0) = X3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f58691,f271])).

fof(f58691,plain,
    ( ! [X3] : k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k5_xboole_0(sK0,X3),sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f255,f58615])).

fof(f58615,plain,
    ( ! [X6] : sK0 = k5_xboole_0(k5_xboole_0(sK0,X6),X6)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f58567,f271])).

fof(f58567,plain,
    ( ! [X6] : sK0 = k5_xboole_0(k5_xboole_0(sK0,X6),k5_xboole_0(k1_xboole_0,X6))
    | ~ spl3_4 ),
    inference(superposition,[],[f58517,f255])).

fof(f58517,plain,
    ( ! [X56] : sK0 = k5_xboole_0(X56,k5_xboole_0(sK0,X56))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f58516,f116])).

fof(f116,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f54,f62])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f30,f29])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f58516,plain,
    ( ! [X56] : k2_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(X56,k5_xboole_0(sK0,X56))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f58515,f6063])).

fof(f6063,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = X0 ),
    inference(resolution,[],[f6039,f34])).

fof(f6039,plain,(
    ! [X12,X13] : r1_tarski(X12,k5_xboole_0(X13,k5_xboole_0(X12,X13))) ),
    inference(forward_demodulation,[],[f6012,f151])).

fof(f6012,plain,(
    ! [X12,X13] : r1_tarski(k4_xboole_0(X12,k1_xboole_0),k5_xboole_0(X13,k5_xboole_0(X12,X13))) ),
    inference(superposition,[],[f5681,f261])).

fof(f5681,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(X8,k5_xboole_0(X8,X9)),X9) ),
    inference(forward_demodulation,[],[f5655,f271])).

fof(f5655,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(X8,k5_xboole_0(X8,X9)),k5_xboole_0(k1_xboole_0,X9)) ),
    inference(superposition,[],[f5595,f255])).

fof(f5595,plain,(
    ! [X48,X49] : r1_tarski(k4_xboole_0(X49,X48),k5_xboole_0(X49,X48)) ),
    inference(forward_demodulation,[],[f5541,f151])).

fof(f5541,plain,(
    ! [X48,X49] : r1_tarski(k4_xboole_0(X49,X48),k4_xboole_0(k5_xboole_0(X49,X48),k1_xboole_0)) ),
    inference(superposition,[],[f1531,f116])).

fof(f58515,plain,
    ( ! [X56] : k5_xboole_0(X56,k5_xboole_0(sK0,X56)) = k2_xboole_0(k3_xboole_0(sK0,k5_xboole_0(X56,k5_xboole_0(sK0,X56))),k1_xboole_0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f58419,f29])).

fof(f58419,plain,
    ( ! [X56] : k5_xboole_0(X56,k5_xboole_0(sK0,X56)) = k2_xboole_0(k3_xboole_0(k5_xboole_0(X56,k5_xboole_0(sK0,X56)),sK0),k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f33,f49920])).

fof(f49920,plain,
    ( ! [X15] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X15,k5_xboole_0(sK0,X15)),sK0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f49857,f152])).

fof(f49857,plain,
    ( ! [X15] : k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k5_xboole_0(X15,k5_xboole_0(sK0,X15)),sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f42200,f261])).

fof(f42200,plain,
    ( ! [X124] : k4_xboole_0(X124,sK0) = k4_xboole_0(k5_xboole_0(sK0,X124),sK0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f42199,f120])).

fof(f120,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f54,f61])).

fof(f61,plain,(
    ! [X2] : k3_xboole_0(X2,X2) = X2 ),
    inference(resolution,[],[f34,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f28,f30])).

fof(f42199,plain,
    ( ! [X124] : k4_xboole_0(k5_xboole_0(sK0,X124),sK0) = k4_xboole_0(X124,k2_xboole_0(sK0,sK0))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f42128,f224])).

fof(f42128,plain,
    ( ! [X124] : k4_xboole_0(k5_xboole_0(sK0,X124),sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X124,k2_xboole_0(sK0,sK0)))
    | ~ spl3_4 ),
    inference(superposition,[],[f38,f41577])).

fof(f41577,plain,
    ( ! [X46] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X46,sK0))
    | ~ spl3_4 ),
    inference(superposition,[],[f150,f41509])).

fof(f83960,plain,
    ( k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK2,sK0),sK1)
    | ~ spl3_17
    | ~ spl3_23 ),
    inference(superposition,[],[f75920,f427])).

fof(f75920,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK1,X0)),sK1)
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f75892,f114])).

fof(f75892,plain,
    ( ! [X0] : k4_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK1,X0)),sK1) = k3_xboole_0(k4_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK1,X0)),sK1),k1_xboole_0)
    | ~ spl3_23 ),
    inference(resolution,[],[f71804,f34])).

fof(f98249,plain,
    ( spl3_51
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f83919,f613,f425,f66,f98246])).

fof(f98246,plain,
    ( spl3_51
  <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f83919,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),sK1),k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f83885,f41509])).

fof(f83885,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK0),sK1),k1_xboole_0)
    | ~ spl3_17
    | ~ spl3_23 ),
    inference(superposition,[],[f75919,f427])).

fof(f78658,plain,
    ( spl3_50
    | ~ spl3_23
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f78613,f78526,f613,f78655])).

fof(f78655,plain,
    ( spl3_50
  <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f78526,plain,
    ( spl3_49
  <=> sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f78613,plain,
    ( sK1 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1)
    | ~ spl3_23
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f78612,f615])).

fof(f78612,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1)
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f78611,f31])).

fof(f78611,plain,
    ( k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1)
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f78571,f65839])).

fof(f65839,plain,(
    ! [X17,X16] : k5_xboole_0(X16,X17) = k5_xboole_0(X17,X16) ),
    inference(forward_demodulation,[],[f65723,f271])).

fof(f65723,plain,(
    ! [X17,X16] : k5_xboole_0(X16,X17) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X17),X16) ),
    inference(superposition,[],[f65556,f255])).

fof(f78571,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,sK2),sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1)
    | ~ spl3_49 ),
    inference(superposition,[],[f31,f78528])).

fof(f78528,plain,
    ( sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f78526])).

fof(f78529,plain,
    ( spl3_49
    | ~ spl3_5
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f78356,f19221,f71,f78526])).

fof(f19221,plain,
    ( spl3_32
  <=> sK1 = k5_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f78356,plain,
    ( sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_5
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f78355,f61])).

fof(f78355,plain,
    ( k3_xboole_0(sK2,sK2) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_5
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f78177,f892])).

fof(f78177,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_5
    | ~ spl3_32 ),
    inference(superposition,[],[f63271,f19223])).

fof(f19223,plain,
    ( sK1 = k5_xboole_0(k4_xboole_0(sK1,sK2),sK2)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f19221])).

fof(f63271,plain,
    ( ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(k5_xboole_0(X0,sK2),X0)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f63270,f120])).

fof(f63270,plain,
    ( ! [X0] : k4_xboole_0(k5_xboole_0(X0,sK2),X0) = k4_xboole_0(sK2,k2_xboole_0(X0,X0))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f63043,f224])).

fof(f63043,plain,
    ( ! [X0] : k4_xboole_0(k5_xboole_0(X0,sK2),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k2_xboole_0(X0,X0)))
    | ~ spl3_5 ),
    inference(superposition,[],[f38,f61686])).

fof(f61686,plain,
    ( ! [X15] : k1_xboole_0 = k4_xboole_0(X15,k2_xboole_0(sK2,X15))
    | ~ spl3_5 ),
    inference(superposition,[],[f150,f61508])).

fof(f64699,plain,
    ( spl3_48
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f63033,f290,f71,f64696])).

fof(f64696,plain,
    ( spl3_48
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f290,plain,
    ( spl3_14
  <=> sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f63033,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(superposition,[],[f61686,f292])).

fof(f292,plain,
    ( sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f290])).

fof(f64453,plain,
    ( spl3_47
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f64384,f64356,f64450])).

fof(f64450,plain,
    ( spl3_47
  <=> sK1 = k2_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f64356,plain,
    ( spl3_46
  <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f64384,plain,
    ( sK1 = k2_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_46 ),
    inference(superposition,[],[f138,f64358])).

fof(f64358,plain,
    ( sK1 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK2)
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f64356])).

fof(f138,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f54,f60])).

fof(f64359,plain,
    ( spl3_46
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f61528,f290,f71,f64356])).

fof(f61528,plain,
    ( sK1 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK2)
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f61499,f271])).

fof(f61499,plain,
    ( k5_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK2)
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(superposition,[],[f60855,f292])).

fof(f50822,plain,
    ( spl3_45
    | ~ spl3_4
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f50728,f19198,f66,f50819])).

fof(f50819,plain,
    ( spl3_45
  <=> sK0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f19198,plain,
    ( spl3_31
  <=> sK1 = k5_xboole_0(k4_xboole_0(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f50728,plain,
    ( sK0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl3_4
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f50727,f61])).

fof(f50727,plain,
    ( k3_xboole_0(sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl3_4
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f50587,f719])).

fof(f50587,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl3_4
    | ~ spl3_31 ),
    inference(superposition,[],[f43619,f19200])).

fof(f19200,plain,
    ( sK1 = k5_xboole_0(k4_xboole_0(sK1,sK0),sK0)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f19198])).

fof(f43619,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(k5_xboole_0(X0,sK0),X0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f43618,f120])).

fof(f43618,plain,
    ( ! [X0] : k4_xboole_0(k5_xboole_0(X0,sK0),X0) = k4_xboole_0(sK0,k2_xboole_0(X0,X0))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f43405,f224])).

fof(f43405,plain,
    ( ! [X0] : k4_xboole_0(k5_xboole_0(X0,sK0),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k2_xboole_0(X0,X0)))
    | ~ spl3_4 ),
    inference(superposition,[],[f38,f41611])).

fof(f41611,plain,
    ( ! [X18] : k1_xboole_0 = k4_xboole_0(X18,k2_xboole_0(sK0,X18))
    | ~ spl3_4 ),
    inference(superposition,[],[f150,f41509])).

fof(f44722,plain,
    ( spl3_44
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f44670,f44573,f44719])).

fof(f44719,plain,
    ( spl3_44
  <=> sK1 = k2_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f44573,plain,
    ( spl3_43
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f44670,plain,
    ( sK1 = k2_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f44624,f27])).

fof(f44624,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl3_43 ),
    inference(superposition,[],[f31,f44575])).

fof(f44575,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK1)
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f44573])).

fof(f44576,plain,
    ( spl3_43
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f43398,f386,f66,f44573])).

fof(f386,plain,
    ( spl3_16
  <=> sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f43398,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK1)
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(superposition,[],[f41611,f388])).

fof(f388,plain,
    ( sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f386])).

fof(f44456,plain,
    ( spl3_42
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f41723,f94,f66,f44453])).

fof(f44453,plain,
    ( spl3_42
  <=> sK2 = k3_xboole_0(k2_xboole_0(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f94,plain,
    ( spl3_8
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f41723,plain,
    ( sK2 = k3_xboole_0(k2_xboole_0(sK0,sK2),sK2)
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(superposition,[],[f4562,f41509])).

fof(f4562,plain,
    ( ! [X14] : sK2 = k3_xboole_0(k2_xboole_0(sK2,X14),sK2)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f4513,f96])).

fof(f96,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f4513,plain,
    ( ! [X14] : k3_xboole_0(sK1,sK2) = k3_xboole_0(k2_xboole_0(sK2,X14),sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f3950,f60])).

fof(f3950,plain,
    ( ! [X65] : k3_xboole_0(X65,sK2) = k3_xboole_0(sK1,k3_xboole_0(sK2,X65))
    | ~ spl3_8 ),
    inference(superposition,[],[f974,f96])).

fof(f974,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f37,f29])).

fof(f44450,plain,
    ( spl3_41
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f41721,f71,f66,f44447])).

fof(f44447,plain,
    ( spl3_41
  <=> r1_tarski(sK2,k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f41721,plain,
    ( r1_tarski(sK2,k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f2176,f41509])).

fof(f2176,plain,
    ( ! [X7] : r1_tarski(sK2,k3_xboole_0(sK1,k2_xboole_0(sK2,X7)))
    | ~ spl3_5 ),
    inference(superposition,[],[f2081,f60])).

fof(f2081,plain,
    ( ! [X21] : r1_tarski(k3_xboole_0(sK2,X21),k3_xboole_0(sK1,X21))
    | ~ spl3_5 ),
    inference(superposition,[],[f237,f971])).

fof(f971,plain,
    ( ! [X34] : k3_xboole_0(sK2,k3_xboole_0(sK1,X34)) = k3_xboole_0(sK2,X34)
    | ~ spl3_5 ),
    inference(superposition,[],[f37,f73])).

fof(f44177,plain,
    ( spl3_40
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f41527,f386,f66,f44174])).

fof(f44174,plain,
    ( spl3_40
  <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f41527,plain,
    ( sK1 = k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f41503,f271])).

fof(f41503,plain,
    ( k5_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)
    | ~ spl3_4
    | ~ spl3_16 ),
    inference(superposition,[],[f40236,f388])).

fof(f31580,plain,
    ( spl3_39
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f5823,f5819,f31577])).

fof(f31577,plain,
    ( spl3_39
  <=> k4_xboole_0(sK1,sK2) = k3_xboole_0(k4_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f5819,plain,
    ( spl3_25
  <=> r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f5823,plain,
    ( k4_xboole_0(sK1,sK2) = k3_xboole_0(k4_xboole_0(sK1,sK2),sK1)
    | ~ spl3_25 ),
    inference(resolution,[],[f5821,f34])).

fof(f5821,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f5819])).

fof(f31575,plain,
    ( spl3_38
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f5817,f5813,f31572])).

fof(f31572,plain,
    ( spl3_38
  <=> k4_xboole_0(sK1,sK0) = k3_xboole_0(k4_xboole_0(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f5813,plain,
    ( spl3_24
  <=> r1_tarski(k4_xboole_0(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f5817,plain,
    ( k4_xboole_0(sK1,sK0) = k3_xboole_0(k4_xboole_0(sK1,sK0),sK1)
    | ~ spl3_24 ),
    inference(resolution,[],[f5815,f34])).

fof(f5815,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),sK1)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f5813])).

fof(f30515,plain,
    ( spl3_37
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f3135,f561,f525,f348,f30512])).

fof(f30512,plain,
    ( spl3_37
  <=> k4_xboole_0(sK1,sK0) = k5_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f348,plain,
    ( spl3_15
  <=> k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f525,plain,
    ( spl3_18
  <=> k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f3135,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(sK0,sK1)
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f3107,f350])).

fof(f350,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f348])).

fof(f3107,plain,
    ( ! [X0] : k5_xboole_0(X0,sK1) = k5_xboole_0(sK1,X0)
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f3088,f563])).

fof(f3088,plain,
    ( ! [X0] : k5_xboole_0(k2_xboole_0(sK0,sK1),X0) = k5_xboole_0(X0,sK1)
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f2938,f534])).

fof(f534,plain,
    ( ! [X0] : k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(sK0,sK1),X0)) = X0
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f531,f271])).

fof(f531,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(sK0,sK1),X0))
    | ~ spl3_18 ),
    inference(superposition,[],[f35,f527])).

fof(f527,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f525])).

fof(f2938,plain,
    ( ! [X2] : k5_xboole_0(k5_xboole_0(sK1,X2),sK1) = X2
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f2928,f271])).

fof(f2928,plain,
    ( ! [X2] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(sK1,X2),sK1)
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f255,f2900])).

fof(f2900,plain,
    ( ! [X0] : sK1 = k5_xboole_0(k5_xboole_0(sK1,X0),X0)
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f2874,f563])).

fof(f2874,plain,
    ( ! [X0] : sK1 = k5_xboole_0(k5_xboole_0(k2_xboole_0(sK0,sK1),X0),X0)
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f2868,f534])).

fof(f2868,plain,
    ( ! [X5] : sK1 = k5_xboole_0(X5,k5_xboole_0(sK1,X5))
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f2867,f27])).

fof(f2867,plain,
    ( ! [X5] : k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(X5,k5_xboole_0(sK1,X5))
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f2853,f563])).

fof(f2853,plain,
    ( ! [X5] : k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(X5,k5_xboole_0(k2_xboole_0(sK0,sK1),X5))
    | ~ spl3_18 ),
    inference(superposition,[],[f534,f261])).

fof(f26189,plain,
    ( spl3_36
    | ~ spl3_13
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f3093,f561,f525,f175,f26186])).

fof(f26186,plain,
    ( spl3_36
  <=> sK2 = k5_xboole_0(k4_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f175,plain,
    ( spl3_13
  <=> k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f3093,plain,
    ( sK2 = k5_xboole_0(k4_xboole_0(sK1,sK2),sK1)
    | ~ spl3_13
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f2938,f177])).

fof(f177,plain,
    ( k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f175])).

fof(f26138,plain,
    ( spl3_35
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f3092,f561,f525,f348,f26135])).

fof(f26135,plain,
    ( spl3_35
  <=> sK0 = k5_xboole_0(k4_xboole_0(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f3092,plain,
    ( sK0 = k5_xboole_0(k4_xboole_0(sK1,sK0),sK1)
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f2938,f350])).

fof(f26093,plain,
    ( spl3_34
    | ~ spl3_13
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f3063,f561,f525,f175,f26090])).

fof(f26090,plain,
    ( spl3_34
  <=> sK2 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f3063,plain,
    ( sK2 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_13
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f2846,f177])).

fof(f2846,plain,
    ( ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = X0
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f534,f563])).

fof(f26043,plain,
    ( spl3_33
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f3062,f561,f525,f348,f26040])).

fof(f26040,plain,
    ( spl3_33
  <=> sK0 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f3062,plain,
    ( sK0 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f2846,f350])).

fof(f19224,plain,
    ( spl3_32
    | ~ spl3_13
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f2913,f561,f525,f175,f19221])).

fof(f2913,plain,
    ( sK1 = k5_xboole_0(k4_xboole_0(sK1,sK2),sK2)
    | ~ spl3_13
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f2900,f177])).

fof(f19201,plain,
    ( spl3_31
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f2912,f561,f525,f348,f19198])).

fof(f2912,plain,
    ( sK1 = k5_xboole_0(k4_xboole_0(sK1,sK0),sK0)
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f2900,f350])).

fof(f13540,plain,
    ( spl3_30
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f13527,f13510,f13537])).

fof(f13537,plain,
    ( spl3_30
  <=> k4_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f13510,plain,
    ( spl3_29
  <=> sK1 = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f13527,plain,
    ( k4_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1)
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f13519,f271])).

fof(f13519,plain,
    ( k5_xboole_0(sK2,sK1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))
    | ~ spl3_29 ),
    inference(superposition,[],[f255,f13512])).

fof(f13512,plain,
    ( sK1 = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f13510])).

fof(f13513,plain,
    ( spl3_29
    | ~ spl3_13
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f2878,f561,f525,f175,f13510])).

fof(f2878,plain,
    ( sK1 = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_13
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f2868,f177])).

fof(f13484,plain,
    ( spl3_28
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f2877,f561,f525,f348,f13481])).

fof(f13481,plain,
    ( spl3_28
  <=> sK1 = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f2877,plain,
    ( sK1 = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f2868,f350])).

fof(f6060,plain,
    ( spl3_27
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f6031,f175,f6057])).

fof(f6057,plain,
    ( spl3_27
  <=> r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f6031,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
    | ~ spl3_13 ),
    inference(superposition,[],[f5681,f177])).

fof(f6055,plain,
    ( spl3_26
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f6030,f348,f6052])).

fof(f6052,plain,
    ( spl3_26
  <=> r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f6030,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0)
    | ~ spl3_15 ),
    inference(superposition,[],[f5681,f350])).

fof(f5822,plain,
    ( spl3_25
    | ~ spl3_13
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f5805,f561,f525,f175,f5819])).

fof(f5805,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ spl3_13
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f5789,f645])).

fof(f645,plain,(
    ! [X15,X16] : k4_xboole_0(X16,X15) = k4_xboole_0(k4_xboole_0(X16,X15),X15) ),
    inference(forward_demodulation,[],[f636,f27])).

fof(f636,plain,(
    ! [X15,X16] : k4_xboole_0(k4_xboole_0(X16,X15),X15) = k5_xboole_0(k4_xboole_0(X16,X15),k1_xboole_0) ),
    inference(superposition,[],[f141,f575])).

fof(f5789,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),sK1)
    | ~ spl3_13
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f5662,f177])).

fof(f5662,plain,
    ( ! [X20] : r1_tarski(k4_xboole_0(k5_xboole_0(sK1,X20),X20),sK1)
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f5595,f2900])).

fof(f5816,plain,
    ( spl3_24
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f5804,f561,f525,f348,f5813])).

fof(f5804,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),sK1)
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f5788,f645])).

fof(f5788,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK0),sK0),sK1)
    | ~ spl3_15
    | ~ spl3_18
    | ~ spl3_21 ),
    inference(superposition,[],[f5662,f350])).

fof(f616,plain,
    ( spl3_23
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f603,f599,f613])).

fof(f599,plain,
    ( spl3_22
  <=> sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f603,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl3_22 ),
    inference(superposition,[],[f601,f271])).

fof(f601,plain,
    ( sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK2,sK1))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f599])).

fof(f602,plain,
    ( spl3_22
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f549,f536,f599])).

fof(f536,plain,
    ( spl3_19
  <=> k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f549,plain,
    ( sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK2,sK1))
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f546,f27])).

fof(f546,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK2,sK1))
    | ~ spl3_19 ),
    inference(superposition,[],[f255,f538])).

fof(f538,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(sK2,sK1))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f536])).

fof(f564,plain,
    ( spl3_21
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f551,f541,f561])).

fof(f541,plain,
    ( spl3_20
  <=> sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f551,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_20 ),
    inference(superposition,[],[f543,f271])).

fof(f543,plain,
    ( sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f541])).

fof(f544,plain,
    ( spl3_20
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f533,f525,f541])).

fof(f533,plain,
    ( sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f530,f27])).

fof(f530,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))
    | ~ spl3_18 ),
    inference(superposition,[],[f255,f527])).

fof(f539,plain,
    ( spl3_19
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f504,f175,f536])).

fof(f504,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(sK2,sK1))
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f477,f31])).

fof(f477,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)))
    | ~ spl3_13 ),
    inference(superposition,[],[f261,f177])).

fof(f528,plain,
    ( spl3_18
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f505,f348,f525])).

fof(f505,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f478,f31])).

fof(f478,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | ~ spl3_15 ),
    inference(superposition,[],[f261,f350])).

fof(f428,plain,
    ( spl3_17
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f416,f348,f425])).

fof(f416,plain,
    ( sK0 = k3_xboole_0(sK1,sK0)
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f415,f271])).

fof(f415,plain,
    ( k3_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f402,f407])).

fof(f402,plain,
    ( k5_xboole_0(k1_xboole_0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl3_15 ),
    inference(superposition,[],[f255,f350])).

fof(f389,plain,
    ( spl3_16
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f359,f66,f386])).

fof(f359,plain,
    ( sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl3_4 ),
    inference(superposition,[],[f205,f68])).

fof(f205,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X2,X1),k4_xboole_0(X1,X2)) = X1 ),
    inference(superposition,[],[f33,f29])).

fof(f351,plain,
    ( spl3_15
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f333,f66,f348])).

fof(f333,plain,
    ( k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f141,f68])).

fof(f293,plain,
    ( spl3_14
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f211,f94,f290])).

fof(f211,plain,
    ( sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl3_8 ),
    inference(superposition,[],[f33,f96])).

fof(f178,plain,
    ( spl3_13
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f147,f94,f175])).

fof(f147,plain,
    ( k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f32,f96])).

fof(f164,plain,
    ( spl3_12
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f154,f71,f161])).

fof(f161,plain,
    ( spl3_12
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f154,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f148,f26])).

fof(f148,plain,
    ( k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f32,f73])).

fof(f159,plain,
    ( spl3_11
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f153,f66,f156])).

fof(f156,plain,
    ( spl3_11
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f153,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f146,f26])).

fof(f146,plain,
    ( k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f32,f68])).

fof(f107,plain,
    ( spl3_10
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f80,f71,f104])).

fof(f104,plain,
    ( spl3_10
  <=> sK2 = k2_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f80,plain,
    ( sK2 = k2_xboole_0(sK2,sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f30,f73])).

fof(f102,plain,
    ( spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f79,f71,f99])).

fof(f99,plain,
    ( spl3_9
  <=> sK1 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f79,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f54,f73])).

fof(f97,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f77,f71,f94])).

fof(f77,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f73,f29])).

fof(f92,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f76,f66,f89])).

fof(f89,plain,
    ( spl3_7
  <=> sK0 = k2_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f76,plain,
    ( sK0 = k2_xboole_0(sK0,sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f30,f68])).

fof(f87,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f75,f66,f84])).

fof(f84,plain,
    ( spl3_6
  <=> sK1 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f75,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f54,f68])).

fof(f74,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f64,f45,f71])).

fof(f45,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f64,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f34,f47])).

fof(f47,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f69,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f63,f40,f66])).

fof(f40,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f63,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f34,f42])).

fof(f42,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f53,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f48,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f22,f40])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:52:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (20902)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (20903)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (20905)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (20906)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (20909)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (20904)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (20918)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (20916)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (20917)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (20910)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (20908)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (20913)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (20912)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (20914)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (20907)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (20901)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.52  % (20915)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.36/0.53  % (20911)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 4.93/1.01  % (20905)Time limit reached!
% 4.93/1.01  % (20905)------------------------------
% 4.93/1.01  % (20905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.93/1.01  % (20905)Termination reason: Time limit
% 4.93/1.01  % (20905)Termination phase: Saturation
% 4.93/1.01  
% 4.93/1.01  % (20905)Memory used [KB]: 12153
% 4.93/1.01  % (20905)Time elapsed: 0.600 s
% 4.93/1.01  % (20905)------------------------------
% 4.93/1.01  % (20905)------------------------------
% 11.74/1.92  % (20906)Time limit reached!
% 11.74/1.92  % (20906)------------------------------
% 11.74/1.92  % (20906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.74/1.92  % (20906)Termination reason: Time limit
% 11.74/1.92  
% 11.74/1.92  % (20906)Memory used [KB]: 20084
% 11.74/1.92  % (20906)Time elapsed: 1.503 s
% 11.74/1.92  % (20906)------------------------------
% 11.74/1.92  % (20906)------------------------------
% 12.55/1.96  % (20907)Time limit reached!
% 12.55/1.96  % (20907)------------------------------
% 12.55/1.96  % (20907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.55/1.96  % (20907)Termination reason: Time limit
% 12.55/1.96  % (20907)Termination phase: Saturation
% 12.55/1.96  
% 12.55/1.96  % (20907)Memory used [KB]: 22771
% 12.55/1.96  % (20907)Time elapsed: 1.541 s
% 12.55/1.96  % (20907)------------------------------
% 12.55/1.96  % (20907)------------------------------
% 14.32/2.23  % (20903)Time limit reached!
% 14.32/2.23  % (20903)------------------------------
% 14.32/2.23  % (20903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.32/2.23  % (20903)Termination reason: Time limit
% 14.32/2.23  % (20903)Termination phase: Saturation
% 14.32/2.23  
% 14.32/2.23  % (20903)Memory used [KB]: 44519
% 14.32/2.23  % (20903)Time elapsed: 1.800 s
% 14.32/2.23  % (20903)------------------------------
% 14.32/2.23  % (20903)------------------------------
% 17.96/2.62  % (20913)Time limit reached!
% 17.96/2.62  % (20913)------------------------------
% 17.96/2.62  % (20913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.96/2.62  % (20913)Termination reason: Time limit
% 17.96/2.62  % (20913)Termination phase: Saturation
% 17.96/2.62  
% 17.96/2.62  % (20913)Memory used [KB]: 33773
% 17.96/2.62  % (20913)Time elapsed: 2.200 s
% 17.96/2.62  % (20913)------------------------------
% 17.96/2.62  % (20913)------------------------------
% 33.24/4.53  % (20901)Refutation found. Thanks to Tanya!
% 33.24/4.53  % SZS status Theorem for theBenchmark
% 33.24/4.53  % SZS output start Proof for theBenchmark
% 33.24/4.53  fof(f115390,plain,(
% 33.24/4.53    $false),
% 33.24/4.53    inference(avatar_sat_refutation,[],[f43,f48,f53,f69,f74,f87,f92,f97,f102,f107,f159,f164,f178,f293,f351,f389,f428,f528,f539,f544,f564,f602,f616,f5816,f5822,f6055,f6060,f13484,f13513,f13540,f19201,f19224,f26043,f26093,f26138,f26189,f30515,f31575,f31580,f44177,f44450,f44456,f44576,f44722,f50822,f64359,f64453,f64699,f78529,f78658,f98249,f98512,f98680,f113818,f113956,f114739,f115336,f115360,f115364])).
% 33.24/4.53  fof(f115364,plain,(
% 33.24/4.53    spl3_3 | ~spl3_5 | ~spl3_23 | ~spl3_56),
% 33.24/4.53    inference(avatar_contradiction_clause,[],[f115363])).
% 33.24/4.53  fof(f115363,plain,(
% 33.24/4.53    $false | (spl3_3 | ~spl3_5 | ~spl3_23 | ~spl3_56)),
% 33.24/4.53    inference(subsumption_resolution,[],[f115362,f52])).
% 33.24/4.53  fof(f52,plain,(
% 33.24/4.53    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) | spl3_3),
% 33.24/4.53    inference(avatar_component_clause,[],[f50])).
% 33.24/4.53  fof(f50,plain,(
% 33.24/4.53    spl3_3 <=> r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 33.24/4.53  fof(f115362,plain,(
% 33.24/4.53    r1_tarski(k5_xboole_0(sK0,sK2),sK1) | (~spl3_5 | ~spl3_23 | ~spl3_56)),
% 33.24/4.53    inference(forward_demodulation,[],[f115292,f615])).
% 33.24/4.53  fof(f615,plain,(
% 33.24/4.53    sK1 = k2_xboole_0(sK2,sK1) | ~spl3_23),
% 33.24/4.53    inference(avatar_component_clause,[],[f613])).
% 33.24/4.53  fof(f613,plain,(
% 33.24/4.53    spl3_23 <=> sK1 = k2_xboole_0(sK2,sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 33.24/4.53  fof(f115292,plain,(
% 33.24/4.53    r1_tarski(k5_xboole_0(sK0,sK2),k2_xboole_0(sK2,sK1)) | (~spl3_5 | ~spl3_56)),
% 33.24/4.53    inference(superposition,[],[f61688,f114738])).
% 33.24/4.53  fof(f114738,plain,(
% 33.24/4.53    k5_xboole_0(sK0,sK2) = k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) | ~spl3_56),
% 33.24/4.53    inference(avatar_component_clause,[],[f114736])).
% 33.24/4.53  fof(f114736,plain,(
% 33.24/4.53    spl3_56 <=> k5_xboole_0(sK0,sK2) = k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 33.24/4.53  fof(f61688,plain,(
% 33.24/4.53    ( ! [X17,X18] : (r1_tarski(k3_xboole_0(X18,X17),k2_xboole_0(sK2,X17))) ) | ~spl3_5),
% 33.24/4.53    inference(superposition,[],[f1104,f61508])).
% 33.24/4.53  fof(f61508,plain,(
% 33.24/4.53    ( ! [X1] : (k2_xboole_0(sK2,X1) = k2_xboole_0(X1,sK2)) ) | ~spl3_5),
% 33.24/4.53    inference(superposition,[],[f60855,f271])).
% 33.24/4.53  fof(f271,plain,(
% 33.24/4.53    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 33.24/4.53    inference(superposition,[],[f224,f173])).
% 33.24/4.53  fof(f173,plain,(
% 33.24/4.53    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 33.24/4.53    inference(superposition,[],[f31,f151])).
% 33.24/4.53  fof(f151,plain,(
% 33.24/4.53    ( ! [X7] : (k4_xboole_0(X7,k1_xboole_0) = X7) )),
% 33.24/4.53    inference(forward_demodulation,[],[f144,f27])).
% 33.24/4.53  fof(f27,plain,(
% 33.24/4.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 33.24/4.53    inference(cnf_transformation,[],[f9])).
% 33.24/4.53  fof(f9,axiom,(
% 33.24/4.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 33.24/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 33.24/4.53  fof(f144,plain,(
% 33.24/4.53    ( ! [X7] : (k4_xboole_0(X7,k1_xboole_0) = k5_xboole_0(X7,k1_xboole_0)) )),
% 33.24/4.53    inference(superposition,[],[f32,f114])).
% 33.24/4.53  fof(f114,plain,(
% 33.24/4.53    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 33.24/4.53    inference(superposition,[],[f62,f29])).
% 33.24/4.53  fof(f29,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 33.24/4.53    inference(cnf_transformation,[],[f1])).
% 33.24/4.53  fof(f1,axiom,(
% 33.24/4.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 33.24/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 33.24/4.53  fof(f62,plain,(
% 33.24/4.53    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)) )),
% 33.24/4.53    inference(resolution,[],[f34,f25])).
% 33.24/4.53  fof(f25,plain,(
% 33.24/4.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 33.24/4.53    inference(cnf_transformation,[],[f6])).
% 33.24/4.53  fof(f6,axiom,(
% 33.24/4.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 33.24/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 33.24/4.53  fof(f34,plain,(
% 33.24/4.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 33.24/4.53    inference(cnf_transformation,[],[f19])).
% 33.24/4.53  fof(f19,plain,(
% 33.24/4.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 33.24/4.53    inference(ennf_transformation,[],[f5])).
% 33.24/4.53  fof(f5,axiom,(
% 33.24/4.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 33.24/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 33.24/4.53  fof(f32,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 33.24/4.53    inference(cnf_transformation,[],[f2])).
% 33.24/4.53  fof(f2,axiom,(
% 33.24/4.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 33.24/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 33.24/4.53  fof(f31,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 33.24/4.53    inference(cnf_transformation,[],[f13])).
% 33.24/4.53  fof(f13,axiom,(
% 33.24/4.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 33.24/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 33.24/4.53  fof(f224,plain,(
% 33.24/4.53    ( ! [X7] : (k2_xboole_0(k1_xboole_0,X7) = X7) )),
% 33.24/4.53    inference(forward_demodulation,[],[f208,f151])).
% 33.24/4.53  fof(f208,plain,(
% 33.24/4.53    ( ! [X7] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X7,k1_xboole_0)) = X7) )),
% 33.24/4.53    inference(superposition,[],[f33,f114])).
% 33.24/4.53  fof(f33,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 33.24/4.53    inference(cnf_transformation,[],[f8])).
% 33.24/4.53  fof(f8,axiom,(
% 33.24/4.53    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 33.24/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 33.24/4.53  fof(f60855,plain,(
% 33.24/4.53    ( ! [X2] : (k2_xboole_0(X2,sK2) = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK2,X2))) ) | ~spl3_5),
% 33.24/4.53    inference(forward_demodulation,[],[f60819,f27])).
% 33.24/4.53  fof(f60819,plain,(
% 33.24/4.53    ( ! [X2] : (k5_xboole_0(k1_xboole_0,k2_xboole_0(sK2,X2)) = k5_xboole_0(k2_xboole_0(X2,sK2),k1_xboole_0)) ) | ~spl3_5),
% 33.24/4.53    inference(superposition,[],[f255,f60338])).
% 33.24/4.53  fof(f60338,plain,(
% 33.24/4.53    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(k2_xboole_0(X4,sK2),k2_xboole_0(sK2,X4))) ) | ~spl3_5),
% 33.24/4.53    inference(forward_demodulation,[],[f60316,f31])).
% 33.24/4.53  fof(f60316,plain,(
% 33.24/4.53    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(k2_xboole_0(X4,sK2),k5_xboole_0(sK2,k4_xboole_0(X4,sK2)))) ) | ~spl3_5),
% 33.24/4.53    inference(superposition,[],[f261,f60283])).
% 33.24/4.53  fof(f60283,plain,(
% 33.24/4.53    ( ! [X0] : (k4_xboole_0(X0,sK2) = k5_xboole_0(k2_xboole_0(X0,sK2),sK2)) ) | ~spl3_5),
% 33.24/4.53    inference(forward_demodulation,[],[f60250,f141])).
% 33.24/4.53  fof(f141,plain,(
% 33.24/4.53    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 33.24/4.53    inference(superposition,[],[f32,f29])).
% 33.24/4.53  fof(f60250,plain,(
% 33.24/4.53    ( ! [X0] : (k5_xboole_0(k2_xboole_0(X0,sK2),sK2) = k5_xboole_0(X0,k3_xboole_0(sK2,X0))) ) | ~spl3_5),
% 33.24/4.53    inference(superposition,[],[f257,f59894])).
% 33.24/4.53  fof(f59894,plain,(
% 33.24/4.53    ( ! [X20] : (k3_xboole_0(sK2,X20) = k5_xboole_0(k4_xboole_0(sK2,X20),sK2)) ) | ~spl3_5),
% 33.24/4.53    inference(forward_demodulation,[],[f59759,f33573])).
% 33.24/4.53  fof(f33573,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 33.24/4.53    inference(forward_demodulation,[],[f33572,f271])).
% 33.24/4.53  fof(f33572,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)),k4_xboole_0(X0,X1))) )),
% 33.24/4.53    inference(forward_demodulation,[],[f33571,f642])).
% 33.24/4.53  fof(f642,plain,(
% 33.24/4.53    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X7,X6)) = X6) )),
% 33.24/4.53    inference(forward_demodulation,[],[f632,f27])).
% 33.24/4.53  fof(f632,plain,(
% 33.24/4.53    ( ! [X6,X7] : (k5_xboole_0(X6,k1_xboole_0) = k4_xboole_0(X6,k4_xboole_0(X7,X6))) )),
% 33.24/4.53    inference(superposition,[],[f32,f575])).
% 33.24/4.53  fof(f575,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 33.24/4.53    inference(superposition,[],[f36,f219])).
% 33.24/4.53  fof(f219,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 33.24/4.53    inference(superposition,[],[f150,f33])).
% 33.24/4.53  fof(f150,plain,(
% 33.24/4.53    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 33.24/4.53    inference(forward_demodulation,[],[f143,f26])).
% 33.24/4.53  fof(f26,plain,(
% 33.24/4.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 33.24/4.53    inference(cnf_transformation,[],[f12])).
% 33.24/4.53  fof(f12,axiom,(
% 33.24/4.53    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 33.24/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 33.24/4.53  fof(f143,plain,(
% 33.24/4.53    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(X5,X5)) )),
% 33.24/4.53    inference(superposition,[],[f32,f60])).
% 33.24/4.53  fof(f60,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 33.24/4.53    inference(resolution,[],[f34,f28])).
% 33.24/4.53  fof(f28,plain,(
% 33.24/4.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 33.24/4.53    inference(cnf_transformation,[],[f10])).
% 33.24/4.53  fof(f10,axiom,(
% 33.24/4.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 33.24/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 33.24/4.53  fof(f36,plain,(
% 33.24/4.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 33.24/4.53    inference(cnf_transformation,[],[f7])).
% 33.24/4.53  fof(f7,axiom,(
% 33.24/4.53    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 33.24/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 33.24/4.53  fof(f33571,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 33.24/4.53    inference(forward_demodulation,[],[f33570,f271])).
% 33.24/4.53  fof(f33570,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))))) )),
% 33.24/4.53    inference(forward_demodulation,[],[f33569,f173])).
% 33.24/4.53  fof(f33569,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))))) )),
% 33.24/4.53    inference(forward_demodulation,[],[f33382,f224])).
% 33.24/4.53  fof(f33382,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)))))) )),
% 33.24/4.53    inference(superposition,[],[f1537,f152])).
% 33.24/4.53  fof(f152,plain,(
% 33.24/4.53    ( ! [X8] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X8)) )),
% 33.24/4.53    inference(forward_demodulation,[],[f145,f26])).
% 33.24/4.53  fof(f145,plain,(
% 33.24/4.53    ( ! [X8] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X8)) )),
% 33.24/4.53    inference(superposition,[],[f32,f62])).
% 33.24/4.53  fof(f1537,plain,(
% 33.24/4.53    ( ! [X14,X12,X13] : (k4_xboole_0(k5_xboole_0(X14,k3_xboole_0(X12,X13)),k4_xboole_0(X12,X13)) = k2_xboole_0(k4_xboole_0(X14,X12),k3_xboole_0(X12,k4_xboole_0(X13,k2_xboole_0(X14,k4_xboole_0(X12,X13)))))) )),
% 33.24/4.53    inference(forward_demodulation,[],[f1478,f36])).
% 33.24/4.53  fof(f1478,plain,(
% 33.24/4.53    ( ! [X14,X12,X13] : (k4_xboole_0(k5_xboole_0(X14,k3_xboole_0(X12,X13)),k4_xboole_0(X12,X13)) = k2_xboole_0(k4_xboole_0(X14,X12),k4_xboole_0(k3_xboole_0(X12,X13),k2_xboole_0(X14,k4_xboole_0(X12,X13))))) )),
% 33.24/4.53    inference(superposition,[],[f38,f33])).
% 33.24/4.53  fof(f38,plain,(
% 33.24/4.53    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 33.24/4.53    inference(cnf_transformation,[],[f14])).
% 33.24/4.53  fof(f14,axiom,(
% 33.24/4.53    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))),
% 33.24/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).
% 33.24/4.53  fof(f59759,plain,(
% 33.24/4.53    ( ! [X20] : (k4_xboole_0(k3_xboole_0(sK2,X20),k4_xboole_0(sK2,X20)) = k5_xboole_0(k4_xboole_0(sK2,X20),sK2)) ) | ~spl3_5),
% 33.24/4.53    inference(superposition,[],[f409,f893])).
% 33.24/4.53  fof(f893,plain,(
% 33.24/4.53    ( ! [X4] : (sK2 = k2_xboole_0(k4_xboole_0(sK2,X4),k3_xboole_0(sK2,X4))) ) | ~spl3_5),
% 33.24/4.53    inference(forward_demodulation,[],[f876,f892])).
% 33.24/4.53  fof(f892,plain,(
% 33.24/4.53    ( ! [X3] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X3)) = k3_xboole_0(sK2,X3)) ) | ~spl3_5),
% 33.24/4.53    inference(forward_demodulation,[],[f875,f407])).
% 33.24/4.53  fof(f407,plain,(
% 33.24/4.53    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 33.24/4.53    inference(forward_demodulation,[],[f394,f271])).
% 33.24/4.53  fof(f394,plain,(
% 33.24/4.53    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 33.24/4.53    inference(superposition,[],[f255,f32])).
% 33.24/4.53  fof(f875,plain,(
% 33.24/4.53    ( ! [X3] : (k4_xboole_0(sK2,k4_xboole_0(sK1,X3)) = k5_xboole_0(sK2,k4_xboole_0(sK2,X3))) ) | ~spl3_5),
% 33.24/4.53    inference(superposition,[],[f32,f574])).
% 33.24/4.53  fof(f574,plain,(
% 33.24/4.53    ( ! [X18] : (k3_xboole_0(sK2,k4_xboole_0(sK1,X18)) = k4_xboole_0(sK2,X18)) ) | ~spl3_5),
% 33.24/4.53    inference(superposition,[],[f36,f73])).
% 33.24/4.53  fof(f73,plain,(
% 33.24/4.53    sK2 = k3_xboole_0(sK2,sK1) | ~spl3_5),
% 33.24/4.53    inference(avatar_component_clause,[],[f71])).
% 33.24/4.53  fof(f71,plain,(
% 33.24/4.53    spl3_5 <=> sK2 = k3_xboole_0(sK2,sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 33.24/4.53  fof(f876,plain,(
% 33.24/4.53    ( ! [X4] : (sK2 = k2_xboole_0(k4_xboole_0(sK2,X4),k4_xboole_0(sK2,k4_xboole_0(sK1,X4)))) ) | ~spl3_5),
% 33.24/4.53    inference(superposition,[],[f33,f574])).
% 33.24/4.53  fof(f409,plain,(
% 33.24/4.53    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k5_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 33.24/4.53    inference(forward_demodulation,[],[f396,f271])).
% 33.24/4.53  fof(f396,plain,(
% 33.24/4.53    ( ! [X6,X5] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X6,X5)) = k5_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 33.24/4.53    inference(superposition,[],[f255,f31])).
% 33.24/4.53  fof(f257,plain,(
% 33.24/4.53    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(k4_xboole_0(X6,X5),X7)) = k5_xboole_0(k2_xboole_0(X5,X6),X7)) )),
% 33.24/4.53    inference(superposition,[],[f35,f31])).
% 33.24/4.53  fof(f35,plain,(
% 33.24/4.53    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 33.24/4.53    inference(cnf_transformation,[],[f11])).
% 33.24/4.53  fof(f11,axiom,(
% 33.24/4.53    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 33.24/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 33.24/4.53  fof(f261,plain,(
% 33.24/4.53    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 33.24/4.53    inference(superposition,[],[f35,f26])).
% 33.24/4.53  fof(f255,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 33.24/4.53    inference(superposition,[],[f35,f26])).
% 33.24/4.53  fof(f1104,plain,(
% 33.24/4.53    ( ! [X12,X13,X11] : (r1_tarski(k3_xboole_0(X13,X11),k2_xboole_0(X11,X12))) )),
% 33.24/4.53    inference(superposition,[],[f991,f60])).
% 33.24/4.53  fof(f991,plain,(
% 33.24/4.53    ( ! [X37,X38,X36] : (r1_tarski(k3_xboole_0(X36,k3_xboole_0(X37,X38)),X38)) )),
% 33.24/4.53    inference(superposition,[],[f237,f37])).
% 33.24/4.53  fof(f37,plain,(
% 33.24/4.53    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 33.24/4.53    inference(cnf_transformation,[],[f3])).
% 33.24/4.53  fof(f3,axiom,(
% 33.24/4.53    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 33.24/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 33.24/4.53  fof(f237,plain,(
% 33.24/4.53    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 33.24/4.53    inference(superposition,[],[f221,f29])).
% 33.24/4.53  fof(f221,plain,(
% 33.24/4.53    ( ! [X4,X5] : (r1_tarski(k3_xboole_0(X4,X5),X4)) )),
% 33.24/4.53    inference(superposition,[],[f28,f33])).
% 33.24/4.53  fof(f115360,plain,(
% 33.24/4.53    spl3_3 | ~spl3_4 | ~spl3_21 | ~spl3_56),
% 33.24/4.53    inference(avatar_contradiction_clause,[],[f115359])).
% 33.24/4.53  fof(f115359,plain,(
% 33.24/4.53    $false | (spl3_3 | ~spl3_4 | ~spl3_21 | ~spl3_56)),
% 33.24/4.53    inference(subsumption_resolution,[],[f115358,f52])).
% 33.24/4.53  fof(f115358,plain,(
% 33.24/4.53    r1_tarski(k5_xboole_0(sK0,sK2),sK1) | (~spl3_4 | ~spl3_21 | ~spl3_56)),
% 33.24/4.53    inference(forward_demodulation,[],[f115288,f563])).
% 33.24/4.53  fof(f563,plain,(
% 33.24/4.53    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_21),
% 33.24/4.53    inference(avatar_component_clause,[],[f561])).
% 33.24/4.53  fof(f561,plain,(
% 33.24/4.53    spl3_21 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 33.24/4.53  fof(f115288,plain,(
% 33.24/4.53    r1_tarski(k5_xboole_0(sK0,sK2),k2_xboole_0(sK0,sK1)) | (~spl3_4 | ~spl3_56)),
% 33.24/4.53    inference(superposition,[],[f41612,f114738])).
% 33.24/4.53  fof(f41612,plain,(
% 33.24/4.53    ( ! [X19,X20] : (r1_tarski(k3_xboole_0(X20,X19),k2_xboole_0(sK0,X19))) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f1104,f41509])).
% 33.24/4.53  fof(f41509,plain,(
% 33.24/4.53    ( ! [X1] : (k2_xboole_0(sK0,X1) = k2_xboole_0(X1,sK0)) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f40236,f271])).
% 33.24/4.53  fof(f40236,plain,(
% 33.24/4.53    ( ! [X2] : (k2_xboole_0(X2,sK0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X2))) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f40204,f27])).
% 33.24/4.53  fof(f40204,plain,(
% 33.24/4.53    ( ! [X2] : (k5_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X2)) = k5_xboole_0(k2_xboole_0(X2,sK0),k1_xboole_0)) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f255,f38146])).
% 33.24/4.53  fof(f38146,plain,(
% 33.24/4.53    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(k2_xboole_0(X4,sK0),k2_xboole_0(sK0,X4))) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f38126,f31])).
% 33.24/4.53  fof(f38126,plain,(
% 33.24/4.53    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(k2_xboole_0(X4,sK0),k5_xboole_0(sK0,k4_xboole_0(X4,sK0)))) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f261,f34928])).
% 33.24/4.53  fof(f34928,plain,(
% 33.24/4.53    ( ! [X1] : (k4_xboole_0(X1,sK0) = k5_xboole_0(k2_xboole_0(X1,sK0),sK0)) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f34891,f141])).
% 33.24/4.53  fof(f34891,plain,(
% 33.24/4.53    ( ! [X1] : (k5_xboole_0(k2_xboole_0(X1,sK0),sK0) = k5_xboole_0(X1,k3_xboole_0(sK0,X1))) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f257,f29637])).
% 33.24/4.53  fof(f29637,plain,(
% 33.24/4.53    ( ! [X10] : (k3_xboole_0(sK0,X10) = k5_xboole_0(k4_xboole_0(sK0,X10),sK0)) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f29599,f719])).
% 33.24/4.53  fof(f719,plain,(
% 33.24/4.53    ( ! [X3] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X3)) = k3_xboole_0(sK0,X3)) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f703,f407])).
% 33.24/4.53  fof(f703,plain,(
% 33.24/4.53    ( ! [X3] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X3)) = k5_xboole_0(sK0,k4_xboole_0(sK0,X3))) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f32,f571])).
% 33.24/4.53  fof(f571,plain,(
% 33.24/4.53    ( ! [X15] : (k3_xboole_0(sK0,k4_xboole_0(sK1,X15)) = k4_xboole_0(sK0,X15)) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f36,f68])).
% 33.24/4.53  fof(f68,plain,(
% 33.24/4.53    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_4),
% 33.24/4.53    inference(avatar_component_clause,[],[f66])).
% 33.24/4.53  fof(f66,plain,(
% 33.24/4.53    spl3_4 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 33.24/4.53  fof(f29599,plain,(
% 33.24/4.53    ( ! [X10] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X10)) = k5_xboole_0(k4_xboole_0(sK0,X10),sK0)) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f21880,f571])).
% 33.24/4.53  fof(f21880,plain,(
% 33.24/4.53    ( ! [X3] : (k4_xboole_0(sK0,X3) = k5_xboole_0(k3_xboole_0(sK0,X3),sK0)) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f21827,f271])).
% 33.24/4.53  fof(f21827,plain,(
% 33.24/4.53    ( ! [X3] : (k5_xboole_0(k3_xboole_0(sK0,X3),sK0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X3))) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f255,f15322])).
% 33.24/4.53  fof(f15322,plain,(
% 33.24/4.53    ( ! [X44] : (sK0 = k5_xboole_0(k3_xboole_0(sK0,X44),k4_xboole_0(sK0,X44))) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f15279,f8723])).
% 33.24/4.53  fof(f8723,plain,(
% 33.24/4.53    ( ! [X3] : (sK0 = k2_xboole_0(k3_xboole_0(sK0,X3),sK0)) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f8713,f719])).
% 33.24/4.53  fof(f8713,plain,(
% 33.24/4.53    ( ! [X31] : (sK0 = k2_xboole_0(k4_xboole_0(sK0,X31),sK0)) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f8681,f6382])).
% 33.24/4.53  fof(f6382,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0) )),
% 33.24/4.53    inference(forward_demodulation,[],[f6299,f27])).
% 33.24/4.53  fof(f6299,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 33.24/4.53    inference(superposition,[],[f256,f26])).
% 33.24/4.53  fof(f256,plain,(
% 33.24/4.53    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X3),X4)) = k5_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 33.24/4.53    inference(superposition,[],[f35,f32])).
% 33.24/4.53  fof(f8681,plain,(
% 33.24/4.53    ( ! [X31] : (k2_xboole_0(k4_xboole_0(sK0,X31),sK0) = k5_xboole_0(k4_xboole_0(sK0,X31),k3_xboole_0(sK0,X31))) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f31,f3510])).
% 33.24/4.53  fof(f3510,plain,(
% 33.24/4.53    ( ! [X21] : (k3_xboole_0(sK0,X21) = k4_xboole_0(sK0,k4_xboole_0(sK0,X21))) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f3491,f407])).
% 33.24/4.53  fof(f3491,plain,(
% 33.24/4.53    ( ! [X21] : (k4_xboole_0(sK0,k4_xboole_0(sK0,X21)) = k5_xboole_0(sK0,k4_xboole_0(sK0,X21))) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f141,f721])).
% 33.24/4.53  fof(f721,plain,(
% 33.24/4.53    ( ! [X0] : (k4_xboole_0(sK0,X0) = k3_xboole_0(k4_xboole_0(sK0,X0),sK0)) ) | ~spl3_4),
% 33.24/4.53    inference(resolution,[],[f710,f34])).
% 33.24/4.53  fof(f710,plain,(
% 33.24/4.53    ( ! [X11] : (r1_tarski(k4_xboole_0(sK0,X11),sK0)) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f221,f571])).
% 33.24/4.53  fof(f15279,plain,(
% 33.24/4.53    ( ! [X44] : (k2_xboole_0(k3_xboole_0(sK0,X44),sK0) = k5_xboole_0(k3_xboole_0(sK0,X44),k4_xboole_0(sK0,X44))) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f31,f8693])).
% 33.24/4.53  fof(f8693,plain,(
% 33.24/4.53    ( ! [X3] : (k4_xboole_0(sK0,X3) = k4_xboole_0(sK0,k3_xboole_0(sK0,X3))) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f8647,f571])).
% 33.24/4.53  fof(f8647,plain,(
% 33.24/4.53    ( ! [X3] : (k3_xboole_0(sK0,k4_xboole_0(sK1,X3)) = k4_xboole_0(sK0,k3_xboole_0(sK0,X3))) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f3510,f719])).
% 33.24/4.53  fof(f115336,plain,(
% 33.24/4.53    spl3_3 | ~spl3_56),
% 33.24/4.53    inference(avatar_contradiction_clause,[],[f115335])).
% 33.24/4.53  fof(f115335,plain,(
% 33.24/4.53    $false | (spl3_3 | ~spl3_56)),
% 33.24/4.53    inference(subsumption_resolution,[],[f115250,f52])).
% 33.24/4.53  fof(f115250,plain,(
% 33.24/4.53    r1_tarski(k5_xboole_0(sK0,sK2),sK1) | ~spl3_56),
% 33.24/4.53    inference(superposition,[],[f237,f114738])).
% 33.24/4.53  fof(f114739,plain,(
% 33.24/4.53    spl3_56 | ~spl3_52),
% 33.24/4.53    inference(avatar_split_clause,[],[f98645,f98509,f114736])).
% 33.24/4.53  fof(f98509,plain,(
% 33.24/4.53    spl3_52 <=> k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK2),sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 33.24/4.53  fof(f98645,plain,(
% 33.24/4.53    k5_xboole_0(sK0,sK2) = k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) | ~spl3_52),
% 33.24/4.53    inference(forward_demodulation,[],[f98572,f27])).
% 33.24/4.53  fof(f98572,plain,(
% 33.24/4.53    k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) = k5_xboole_0(k5_xboole_0(sK0,sK2),k1_xboole_0) | ~spl3_52),
% 33.24/4.53    inference(superposition,[],[f407,f98511])).
% 33.24/4.53  fof(f98511,plain,(
% 33.24/4.53    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK2),sK1) | ~spl3_52),
% 33.24/4.53    inference(avatar_component_clause,[],[f98509])).
% 33.24/4.53  fof(f113956,plain,(
% 33.24/4.53    spl3_55 | ~spl3_54),
% 33.24/4.53    inference(avatar_split_clause,[],[f113928,f113815,f113953])).
% 33.24/4.53  fof(f113953,plain,(
% 33.24/4.53    spl3_55 <=> sK1 = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 33.24/4.53  fof(f113815,plain,(
% 33.24/4.53    spl3_54 <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 33.24/4.53  fof(f113928,plain,(
% 33.24/4.53    sK1 = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | ~spl3_54),
% 33.24/4.53    inference(forward_demodulation,[],[f113869,f27])).
% 33.24/4.53  fof(f113869,plain,(
% 33.24/4.53    k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | ~spl3_54),
% 33.24/4.53    inference(superposition,[],[f31,f113817])).
% 33.24/4.53  fof(f113817,plain,(
% 33.24/4.53    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK0,sK2),sK1) | ~spl3_54),
% 33.24/4.53    inference(avatar_component_clause,[],[f113815])).
% 33.24/4.53  fof(f113818,plain,(
% 33.24/4.53    spl3_54 | ~spl3_4 | ~spl3_17 | ~spl3_23),
% 33.24/4.53    inference(avatar_split_clause,[],[f98169,f613,f425,f66,f113815])).
% 33.24/4.53  fof(f425,plain,(
% 33.24/4.53    spl3_17 <=> sK0 = k3_xboole_0(sK1,sK0)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 33.24/4.53  fof(f98169,plain,(
% 33.24/4.53    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK0,sK2),sK1) | (~spl3_4 | ~spl3_17 | ~spl3_23)),
% 33.24/4.53    inference(forward_demodulation,[],[f98066,f41509])).
% 33.24/4.53  fof(f98066,plain,(
% 33.24/4.53    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK2,sK0),sK1) | (~spl3_17 | ~spl3_23)),
% 33.24/4.53    inference(superposition,[],[f83908,f427])).
% 33.24/4.53  fof(f427,plain,(
% 33.24/4.53    sK0 = k3_xboole_0(sK1,sK0) | ~spl3_17),
% 33.24/4.53    inference(avatar_component_clause,[],[f425])).
% 33.24/4.53  fof(f83908,plain,(
% 33.24/4.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK2,k3_xboole_0(sK1,X0)),sK1)) ) | ~spl3_23),
% 33.24/4.53    inference(forward_demodulation,[],[f83874,f114])).
% 33.24/4.53  fof(f83874,plain,(
% 33.24/4.53    ( ! [X0] : (k4_xboole_0(k2_xboole_0(sK2,k3_xboole_0(sK1,X0)),sK1) = k3_xboole_0(k4_xboole_0(k2_xboole_0(sK2,k3_xboole_0(sK1,X0)),sK1),k1_xboole_0)) ) | ~spl3_23),
% 33.24/4.53    inference(resolution,[],[f75919,f34])).
% 33.24/4.53  fof(f75919,plain,(
% 33.24/4.53    ( ! [X0] : (r1_tarski(k4_xboole_0(k2_xboole_0(sK2,k3_xboole_0(sK1,X0)),sK1),k1_xboole_0)) ) | ~spl3_23),
% 33.24/4.53    inference(superposition,[],[f71804,f585])).
% 33.24/4.53  fof(f585,plain,(
% 33.24/4.53    ( ! [X14,X12,X13] : (k2_xboole_0(X14,k3_xboole_0(X12,X13)) = k5_xboole_0(X14,k3_xboole_0(X12,k4_xboole_0(X13,X14)))) )),
% 33.24/4.53    inference(superposition,[],[f31,f36])).
% 33.24/4.53  fof(f71804,plain,(
% 33.24/4.53    ( ! [X14] : (r1_tarski(k4_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK1,X14)),sK1),k1_xboole_0)) ) | ~spl3_23),
% 33.24/4.53    inference(superposition,[],[f65838,f219])).
% 33.24/4.53  fof(f65838,plain,(
% 33.24/4.53    ( ! [X70] : (r1_tarski(k4_xboole_0(k5_xboole_0(sK2,X70),sK1),k4_xboole_0(X70,sK1))) ) | ~spl3_23),
% 33.24/4.53    inference(superposition,[],[f5548,f65556])).
% 33.24/4.53  fof(f65556,plain,(
% 33.24/4.53    ( ! [X14,X15] : (k5_xboole_0(k5_xboole_0(X15,X14),X15) = X14) )),
% 33.24/4.53    inference(superposition,[],[f62139,f62139])).
% 33.24/4.53  fof(f62139,plain,(
% 33.24/4.53    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,X2)) = X3) )),
% 33.24/4.53    inference(superposition,[],[f515,f271])).
% 33.24/4.53  fof(f515,plain,(
% 33.24/4.53    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k5_xboole_0(X2,X3))) = X2) )),
% 33.24/4.53    inference(forward_demodulation,[],[f489,f27])).
% 33.24/4.53  fof(f489,plain,(
% 33.24/4.53    ( ! [X2,X3] : (k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X3,k5_xboole_0(X2,X3)))) )),
% 33.24/4.53    inference(superposition,[],[f255,f261])).
% 33.24/4.53  fof(f5548,plain,(
% 33.24/4.53    ( ! [X59] : (r1_tarski(k4_xboole_0(X59,sK1),k4_xboole_0(k5_xboole_0(X59,sK2),sK1))) ) | ~spl3_23),
% 33.24/4.53    inference(superposition,[],[f1531,f615])).
% 33.24/4.53  fof(f1531,plain,(
% 33.24/4.53    ( ! [X10,X8,X9] : (r1_tarski(k4_xboole_0(X8,k2_xboole_0(X9,X10)),k4_xboole_0(k5_xboole_0(X8,X9),X10))) )),
% 33.24/4.53    inference(superposition,[],[f28,f38])).
% 33.24/4.53  fof(f98680,plain,(
% 33.24/4.53    spl3_53 | ~spl3_52),
% 33.24/4.53    inference(avatar_split_clause,[],[f98642,f98509,f98677])).
% 33.24/4.53  fof(f98677,plain,(
% 33.24/4.53    spl3_53 <=> sK1 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK2))),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 33.24/4.53  fof(f98642,plain,(
% 33.24/4.53    sK1 = k2_xboole_0(sK1,k5_xboole_0(sK0,sK2)) | ~spl3_52),
% 33.24/4.53    inference(forward_demodulation,[],[f98568,f27])).
% 33.24/4.53  fof(f98568,plain,(
% 33.24/4.53    k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k5_xboole_0(sK0,sK2)) | ~spl3_52),
% 33.24/4.53    inference(superposition,[],[f31,f98511])).
% 33.24/4.53  fof(f98512,plain,(
% 33.24/4.53    spl3_52 | ~spl3_4 | ~spl3_17 | ~spl3_23),
% 33.24/4.53    inference(avatar_split_clause,[],[f84062,f613,f425,f66,f98509])).
% 33.24/4.53  fof(f84062,plain,(
% 33.24/4.53    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK2),sK1) | (~spl3_4 | ~spl3_17 | ~spl3_23)),
% 33.24/4.53    inference(forward_demodulation,[],[f83960,f58842])).
% 33.24/4.53  fof(f58842,plain,(
% 33.24/4.53    ( ! [X6] : (k5_xboole_0(sK0,X6) = k5_xboole_0(X6,sK0)) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f58816,f271])).
% 33.24/4.53  fof(f58816,plain,(
% 33.24/4.53    ( ! [X6] : (k5_xboole_0(sK0,X6) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X6),sK0)) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f58723,f255])).
% 33.24/4.53  fof(f58723,plain,(
% 33.24/4.53    ( ! [X3] : (k5_xboole_0(k5_xboole_0(sK0,X3),sK0) = X3) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f58691,f271])).
% 33.24/4.53  fof(f58691,plain,(
% 33.24/4.53    ( ! [X3] : (k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k5_xboole_0(sK0,X3),sK0)) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f255,f58615])).
% 33.24/4.53  fof(f58615,plain,(
% 33.24/4.53    ( ! [X6] : (sK0 = k5_xboole_0(k5_xboole_0(sK0,X6),X6)) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f58567,f271])).
% 33.24/4.53  fof(f58567,plain,(
% 33.24/4.53    ( ! [X6] : (sK0 = k5_xboole_0(k5_xboole_0(sK0,X6),k5_xboole_0(k1_xboole_0,X6))) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f58517,f255])).
% 33.24/4.53  fof(f58517,plain,(
% 33.24/4.53    ( ! [X56] : (sK0 = k5_xboole_0(X56,k5_xboole_0(sK0,X56))) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f58516,f116])).
% 33.24/4.53  fof(f116,plain,(
% 33.24/4.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 33.24/4.53    inference(superposition,[],[f54,f62])).
% 33.24/4.53  fof(f54,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 33.24/4.53    inference(superposition,[],[f30,f29])).
% 33.24/4.53  fof(f30,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 33.24/4.53    inference(cnf_transformation,[],[f4])).
% 33.24/4.53  fof(f4,axiom,(
% 33.24/4.53    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 33.24/4.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 33.24/4.53  fof(f58516,plain,(
% 33.24/4.53    ( ! [X56] : (k2_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(X56,k5_xboole_0(sK0,X56))) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f58515,f6063])).
% 33.24/4.53  fof(f6063,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = X0) )),
% 33.24/4.53    inference(resolution,[],[f6039,f34])).
% 33.24/4.53  fof(f6039,plain,(
% 33.24/4.53    ( ! [X12,X13] : (r1_tarski(X12,k5_xboole_0(X13,k5_xboole_0(X12,X13)))) )),
% 33.24/4.53    inference(forward_demodulation,[],[f6012,f151])).
% 33.24/4.53  fof(f6012,plain,(
% 33.24/4.53    ( ! [X12,X13] : (r1_tarski(k4_xboole_0(X12,k1_xboole_0),k5_xboole_0(X13,k5_xboole_0(X12,X13)))) )),
% 33.24/4.53    inference(superposition,[],[f5681,f261])).
% 33.24/4.53  fof(f5681,plain,(
% 33.24/4.53    ( ! [X8,X9] : (r1_tarski(k4_xboole_0(X8,k5_xboole_0(X8,X9)),X9)) )),
% 33.24/4.53    inference(forward_demodulation,[],[f5655,f271])).
% 33.24/4.53  fof(f5655,plain,(
% 33.24/4.53    ( ! [X8,X9] : (r1_tarski(k4_xboole_0(X8,k5_xboole_0(X8,X9)),k5_xboole_0(k1_xboole_0,X9))) )),
% 33.24/4.53    inference(superposition,[],[f5595,f255])).
% 33.24/4.53  fof(f5595,plain,(
% 33.24/4.53    ( ! [X48,X49] : (r1_tarski(k4_xboole_0(X49,X48),k5_xboole_0(X49,X48))) )),
% 33.24/4.53    inference(forward_demodulation,[],[f5541,f151])).
% 33.24/4.53  fof(f5541,plain,(
% 33.24/4.53    ( ! [X48,X49] : (r1_tarski(k4_xboole_0(X49,X48),k4_xboole_0(k5_xboole_0(X49,X48),k1_xboole_0))) )),
% 33.24/4.53    inference(superposition,[],[f1531,f116])).
% 33.24/4.53  fof(f58515,plain,(
% 33.24/4.53    ( ! [X56] : (k5_xboole_0(X56,k5_xboole_0(sK0,X56)) = k2_xboole_0(k3_xboole_0(sK0,k5_xboole_0(X56,k5_xboole_0(sK0,X56))),k1_xboole_0)) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f58419,f29])).
% 33.24/4.53  fof(f58419,plain,(
% 33.24/4.53    ( ! [X56] : (k5_xboole_0(X56,k5_xboole_0(sK0,X56)) = k2_xboole_0(k3_xboole_0(k5_xboole_0(X56,k5_xboole_0(sK0,X56)),sK0),k1_xboole_0)) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f33,f49920])).
% 33.24/4.53  fof(f49920,plain,(
% 33.24/4.53    ( ! [X15] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X15,k5_xboole_0(sK0,X15)),sK0)) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f49857,f152])).
% 33.24/4.53  fof(f49857,plain,(
% 33.24/4.53    ( ! [X15] : (k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k5_xboole_0(X15,k5_xboole_0(sK0,X15)),sK0)) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f42200,f261])).
% 33.24/4.53  fof(f42200,plain,(
% 33.24/4.53    ( ! [X124] : (k4_xboole_0(X124,sK0) = k4_xboole_0(k5_xboole_0(sK0,X124),sK0)) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f42199,f120])).
% 33.24/4.53  fof(f120,plain,(
% 33.24/4.53    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 33.24/4.53    inference(superposition,[],[f54,f61])).
% 33.24/4.53  fof(f61,plain,(
% 33.24/4.53    ( ! [X2] : (k3_xboole_0(X2,X2) = X2) )),
% 33.24/4.53    inference(resolution,[],[f34,f56])).
% 33.24/4.53  fof(f56,plain,(
% 33.24/4.53    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 33.24/4.53    inference(superposition,[],[f28,f30])).
% 33.24/4.53  fof(f42199,plain,(
% 33.24/4.53    ( ! [X124] : (k4_xboole_0(k5_xboole_0(sK0,X124),sK0) = k4_xboole_0(X124,k2_xboole_0(sK0,sK0))) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f42128,f224])).
% 33.24/4.53  fof(f42128,plain,(
% 33.24/4.53    ( ! [X124] : (k4_xboole_0(k5_xboole_0(sK0,X124),sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X124,k2_xboole_0(sK0,sK0)))) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f38,f41577])).
% 33.24/4.53  fof(f41577,plain,(
% 33.24/4.53    ( ! [X46] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X46,sK0))) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f150,f41509])).
% 33.24/4.53  fof(f83960,plain,(
% 33.24/4.53    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK2,sK0),sK1) | (~spl3_17 | ~spl3_23)),
% 33.24/4.53    inference(superposition,[],[f75920,f427])).
% 33.24/4.53  fof(f75920,plain,(
% 33.24/4.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK1,X0)),sK1)) ) | ~spl3_23),
% 33.24/4.53    inference(forward_demodulation,[],[f75892,f114])).
% 33.24/4.53  fof(f75892,plain,(
% 33.24/4.53    ( ! [X0] : (k4_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK1,X0)),sK1) = k3_xboole_0(k4_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK1,X0)),sK1),k1_xboole_0)) ) | ~spl3_23),
% 33.24/4.53    inference(resolution,[],[f71804,f34])).
% 33.24/4.53  fof(f98249,plain,(
% 33.24/4.53    spl3_51 | ~spl3_4 | ~spl3_17 | ~spl3_23),
% 33.24/4.53    inference(avatar_split_clause,[],[f83919,f613,f425,f66,f98246])).
% 33.24/4.53  fof(f98246,plain,(
% 33.24/4.53    spl3_51 <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),sK1),k1_xboole_0)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 33.24/4.53  fof(f83919,plain,(
% 33.24/4.53    r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK2),sK1),k1_xboole_0) | (~spl3_4 | ~spl3_17 | ~spl3_23)),
% 33.24/4.53    inference(forward_demodulation,[],[f83885,f41509])).
% 33.24/4.53  fof(f83885,plain,(
% 33.24/4.53    r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK0),sK1),k1_xboole_0) | (~spl3_17 | ~spl3_23)),
% 33.24/4.53    inference(superposition,[],[f75919,f427])).
% 33.24/4.53  fof(f78658,plain,(
% 33.24/4.53    spl3_50 | ~spl3_23 | ~spl3_49),
% 33.24/4.53    inference(avatar_split_clause,[],[f78613,f78526,f613,f78655])).
% 33.24/4.53  fof(f78655,plain,(
% 33.24/4.53    spl3_50 <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 33.24/4.53  fof(f78526,plain,(
% 33.24/4.53    spl3_49 <=> sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 33.24/4.53  fof(f78613,plain,(
% 33.24/4.53    sK1 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) | (~spl3_23 | ~spl3_49)),
% 33.24/4.53    inference(forward_demodulation,[],[f78612,f615])).
% 33.24/4.53  fof(f78612,plain,(
% 33.24/4.53    k2_xboole_0(sK2,sK1) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) | ~spl3_49),
% 33.24/4.53    inference(forward_demodulation,[],[f78611,f31])).
% 33.24/4.53  fof(f78611,plain,(
% 33.24/4.53    k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) | ~spl3_49),
% 33.24/4.53    inference(forward_demodulation,[],[f78571,f65839])).
% 33.24/4.53  fof(f65839,plain,(
% 33.24/4.53    ( ! [X17,X16] : (k5_xboole_0(X16,X17) = k5_xboole_0(X17,X16)) )),
% 33.24/4.53    inference(forward_demodulation,[],[f65723,f271])).
% 33.24/4.53  fof(f65723,plain,(
% 33.24/4.53    ( ! [X17,X16] : (k5_xboole_0(X16,X17) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X17),X16)) )),
% 33.24/4.53    inference(superposition,[],[f65556,f255])).
% 33.24/4.53  fof(f78571,plain,(
% 33.24/4.53    k5_xboole_0(k4_xboole_0(sK1,sK2),sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) | ~spl3_49),
% 33.24/4.53    inference(superposition,[],[f31,f78528])).
% 33.24/4.53  fof(f78528,plain,(
% 33.24/4.53    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl3_49),
% 33.24/4.53    inference(avatar_component_clause,[],[f78526])).
% 33.24/4.53  fof(f78529,plain,(
% 33.24/4.53    spl3_49 | ~spl3_5 | ~spl3_32),
% 33.24/4.53    inference(avatar_split_clause,[],[f78356,f19221,f71,f78526])).
% 33.24/4.53  fof(f19221,plain,(
% 33.24/4.53    spl3_32 <=> sK1 = k5_xboole_0(k4_xboole_0(sK1,sK2),sK2)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 33.24/4.53  fof(f78356,plain,(
% 33.24/4.53    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | (~spl3_5 | ~spl3_32)),
% 33.24/4.53    inference(forward_demodulation,[],[f78355,f61])).
% 33.24/4.53  fof(f78355,plain,(
% 33.24/4.53    k3_xboole_0(sK2,sK2) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | (~spl3_5 | ~spl3_32)),
% 33.24/4.53    inference(forward_demodulation,[],[f78177,f892])).
% 33.24/4.53  fof(f78177,plain,(
% 33.24/4.53    k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | (~spl3_5 | ~spl3_32)),
% 33.24/4.53    inference(superposition,[],[f63271,f19223])).
% 33.24/4.53  fof(f19223,plain,(
% 33.24/4.53    sK1 = k5_xboole_0(k4_xboole_0(sK1,sK2),sK2) | ~spl3_32),
% 33.24/4.53    inference(avatar_component_clause,[],[f19221])).
% 33.24/4.53  fof(f63271,plain,(
% 33.24/4.53    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(k5_xboole_0(X0,sK2),X0)) ) | ~spl3_5),
% 33.24/4.53    inference(forward_demodulation,[],[f63270,f120])).
% 33.24/4.53  fof(f63270,plain,(
% 33.24/4.53    ( ! [X0] : (k4_xboole_0(k5_xboole_0(X0,sK2),X0) = k4_xboole_0(sK2,k2_xboole_0(X0,X0))) ) | ~spl3_5),
% 33.24/4.53    inference(forward_demodulation,[],[f63043,f224])).
% 33.24/4.53  fof(f63043,plain,(
% 33.24/4.53    ( ! [X0] : (k4_xboole_0(k5_xboole_0(X0,sK2),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k2_xboole_0(X0,X0)))) ) | ~spl3_5),
% 33.24/4.53    inference(superposition,[],[f38,f61686])).
% 33.24/4.53  fof(f61686,plain,(
% 33.24/4.53    ( ! [X15] : (k1_xboole_0 = k4_xboole_0(X15,k2_xboole_0(sK2,X15))) ) | ~spl3_5),
% 33.24/4.53    inference(superposition,[],[f150,f61508])).
% 33.24/4.53  fof(f64699,plain,(
% 33.24/4.53    spl3_48 | ~spl3_5 | ~spl3_14),
% 33.24/4.53    inference(avatar_split_clause,[],[f63033,f290,f71,f64696])).
% 33.24/4.53  fof(f64696,plain,(
% 33.24/4.53    spl3_48 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 33.24/4.53  fof(f290,plain,(
% 33.24/4.53    spl3_14 <=> sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 33.24/4.53  fof(f63033,plain,(
% 33.24/4.53    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),sK1) | (~spl3_5 | ~spl3_14)),
% 33.24/4.53    inference(superposition,[],[f61686,f292])).
% 33.24/4.53  fof(f292,plain,(
% 33.24/4.53    sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~spl3_14),
% 33.24/4.53    inference(avatar_component_clause,[],[f290])).
% 33.24/4.53  fof(f64453,plain,(
% 33.24/4.53    spl3_47 | ~spl3_46),
% 33.24/4.53    inference(avatar_split_clause,[],[f64384,f64356,f64450])).
% 33.24/4.53  fof(f64450,plain,(
% 33.24/4.53    spl3_47 <=> sK1 = k2_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 33.24/4.53  fof(f64356,plain,(
% 33.24/4.53    spl3_46 <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK2)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 33.24/4.53  fof(f64384,plain,(
% 33.24/4.53    sK1 = k2_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl3_46),
% 33.24/4.53    inference(superposition,[],[f138,f64358])).
% 33.24/4.53  fof(f64358,plain,(
% 33.24/4.53    sK1 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK2) | ~spl3_46),
% 33.24/4.53    inference(avatar_component_clause,[],[f64356])).
% 33.24/4.53  fof(f138,plain,(
% 33.24/4.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0)) )),
% 33.24/4.53    inference(superposition,[],[f54,f60])).
% 33.24/4.53  fof(f64359,plain,(
% 33.24/4.53    spl3_46 | ~spl3_5 | ~spl3_14),
% 33.24/4.53    inference(avatar_split_clause,[],[f61528,f290,f71,f64356])).
% 33.24/4.53  fof(f61528,plain,(
% 33.24/4.53    sK1 = k2_xboole_0(k4_xboole_0(sK1,sK2),sK2) | (~spl3_5 | ~spl3_14)),
% 33.24/4.53    inference(forward_demodulation,[],[f61499,f271])).
% 33.24/4.53  fof(f61499,plain,(
% 33.24/4.53    k5_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK2) | (~spl3_5 | ~spl3_14)),
% 33.24/4.53    inference(superposition,[],[f60855,f292])).
% 33.24/4.53  fof(f50822,plain,(
% 33.24/4.53    spl3_45 | ~spl3_4 | ~spl3_31),
% 33.24/4.53    inference(avatar_split_clause,[],[f50728,f19198,f66,f50819])).
% 33.24/4.53  fof(f50819,plain,(
% 33.24/4.53    spl3_45 <=> sK0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 33.24/4.53  fof(f19198,plain,(
% 33.24/4.53    spl3_31 <=> sK1 = k5_xboole_0(k4_xboole_0(sK1,sK0),sK0)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 33.24/4.53  fof(f50728,plain,(
% 33.24/4.53    sK0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | (~spl3_4 | ~spl3_31)),
% 33.24/4.53    inference(forward_demodulation,[],[f50727,f61])).
% 33.24/4.53  fof(f50727,plain,(
% 33.24/4.53    k3_xboole_0(sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | (~spl3_4 | ~spl3_31)),
% 33.24/4.53    inference(forward_demodulation,[],[f50587,f719])).
% 33.24/4.53  fof(f50587,plain,(
% 33.24/4.53    k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | (~spl3_4 | ~spl3_31)),
% 33.24/4.53    inference(superposition,[],[f43619,f19200])).
% 33.24/4.53  fof(f19200,plain,(
% 33.24/4.53    sK1 = k5_xboole_0(k4_xboole_0(sK1,sK0),sK0) | ~spl3_31),
% 33.24/4.53    inference(avatar_component_clause,[],[f19198])).
% 33.24/4.53  fof(f43619,plain,(
% 33.24/4.53    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(k5_xboole_0(X0,sK0),X0)) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f43618,f120])).
% 33.24/4.53  fof(f43618,plain,(
% 33.24/4.53    ( ! [X0] : (k4_xboole_0(k5_xboole_0(X0,sK0),X0) = k4_xboole_0(sK0,k2_xboole_0(X0,X0))) ) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f43405,f224])).
% 33.24/4.53  fof(f43405,plain,(
% 33.24/4.53    ( ! [X0] : (k4_xboole_0(k5_xboole_0(X0,sK0),X0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k2_xboole_0(X0,X0)))) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f38,f41611])).
% 33.24/4.53  fof(f41611,plain,(
% 33.24/4.53    ( ! [X18] : (k1_xboole_0 = k4_xboole_0(X18,k2_xboole_0(sK0,X18))) ) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f150,f41509])).
% 33.24/4.53  fof(f44722,plain,(
% 33.24/4.53    spl3_44 | ~spl3_43),
% 33.24/4.53    inference(avatar_split_clause,[],[f44670,f44573,f44719])).
% 33.24/4.53  fof(f44719,plain,(
% 33.24/4.53    spl3_44 <=> sK1 = k2_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 33.24/4.53  fof(f44573,plain,(
% 33.24/4.53    spl3_43 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 33.24/4.53  fof(f44670,plain,(
% 33.24/4.53    sK1 = k2_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | ~spl3_43),
% 33.24/4.53    inference(forward_demodulation,[],[f44624,f27])).
% 33.24/4.53  fof(f44624,plain,(
% 33.24/4.53    k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | ~spl3_43),
% 33.24/4.53    inference(superposition,[],[f31,f44575])).
% 33.24/4.53  fof(f44575,plain,(
% 33.24/4.53    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK1) | ~spl3_43),
% 33.24/4.53    inference(avatar_component_clause,[],[f44573])).
% 33.24/4.53  fof(f44576,plain,(
% 33.24/4.53    spl3_43 | ~spl3_4 | ~spl3_16),
% 33.24/4.53    inference(avatar_split_clause,[],[f43398,f386,f66,f44573])).
% 33.24/4.53  fof(f386,plain,(
% 33.24/4.53    spl3_16 <=> sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 33.24/4.53  fof(f43398,plain,(
% 33.24/4.53    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK1) | (~spl3_4 | ~spl3_16)),
% 33.24/4.53    inference(superposition,[],[f41611,f388])).
% 33.24/4.53  fof(f388,plain,(
% 33.24/4.53    sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | ~spl3_16),
% 33.24/4.53    inference(avatar_component_clause,[],[f386])).
% 33.24/4.53  fof(f44456,plain,(
% 33.24/4.53    spl3_42 | ~spl3_4 | ~spl3_8),
% 33.24/4.53    inference(avatar_split_clause,[],[f41723,f94,f66,f44453])).
% 33.24/4.53  fof(f44453,plain,(
% 33.24/4.53    spl3_42 <=> sK2 = k3_xboole_0(k2_xboole_0(sK0,sK2),sK2)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 33.24/4.53  fof(f94,plain,(
% 33.24/4.53    spl3_8 <=> sK2 = k3_xboole_0(sK1,sK2)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 33.24/4.53  fof(f41723,plain,(
% 33.24/4.53    sK2 = k3_xboole_0(k2_xboole_0(sK0,sK2),sK2) | (~spl3_4 | ~spl3_8)),
% 33.24/4.53    inference(superposition,[],[f4562,f41509])).
% 33.24/4.53  fof(f4562,plain,(
% 33.24/4.53    ( ! [X14] : (sK2 = k3_xboole_0(k2_xboole_0(sK2,X14),sK2)) ) | ~spl3_8),
% 33.24/4.53    inference(forward_demodulation,[],[f4513,f96])).
% 33.24/4.53  fof(f96,plain,(
% 33.24/4.53    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_8),
% 33.24/4.53    inference(avatar_component_clause,[],[f94])).
% 33.24/4.53  fof(f4513,plain,(
% 33.24/4.53    ( ! [X14] : (k3_xboole_0(sK1,sK2) = k3_xboole_0(k2_xboole_0(sK2,X14),sK2)) ) | ~spl3_8),
% 33.24/4.53    inference(superposition,[],[f3950,f60])).
% 33.24/4.53  fof(f3950,plain,(
% 33.24/4.53    ( ! [X65] : (k3_xboole_0(X65,sK2) = k3_xboole_0(sK1,k3_xboole_0(sK2,X65))) ) | ~spl3_8),
% 33.24/4.53    inference(superposition,[],[f974,f96])).
% 33.24/4.53  fof(f974,plain,(
% 33.24/4.53    ( ! [X6,X7,X5] : (k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6))) )),
% 33.24/4.53    inference(superposition,[],[f37,f29])).
% 33.24/4.53  fof(f44450,plain,(
% 33.24/4.53    spl3_41 | ~spl3_4 | ~spl3_5),
% 33.24/4.53    inference(avatar_split_clause,[],[f41721,f71,f66,f44447])).
% 33.24/4.53  fof(f44447,plain,(
% 33.24/4.53    spl3_41 <=> r1_tarski(sK2,k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)))),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 33.24/4.53  fof(f41721,plain,(
% 33.24/4.53    r1_tarski(sK2,k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))) | (~spl3_4 | ~spl3_5)),
% 33.24/4.53    inference(superposition,[],[f2176,f41509])).
% 33.24/4.53  fof(f2176,plain,(
% 33.24/4.53    ( ! [X7] : (r1_tarski(sK2,k3_xboole_0(sK1,k2_xboole_0(sK2,X7)))) ) | ~spl3_5),
% 33.24/4.53    inference(superposition,[],[f2081,f60])).
% 33.24/4.53  fof(f2081,plain,(
% 33.24/4.53    ( ! [X21] : (r1_tarski(k3_xboole_0(sK2,X21),k3_xboole_0(sK1,X21))) ) | ~spl3_5),
% 33.24/4.53    inference(superposition,[],[f237,f971])).
% 33.24/4.53  fof(f971,plain,(
% 33.24/4.53    ( ! [X34] : (k3_xboole_0(sK2,k3_xboole_0(sK1,X34)) = k3_xboole_0(sK2,X34)) ) | ~spl3_5),
% 33.24/4.53    inference(superposition,[],[f37,f73])).
% 33.24/4.53  fof(f44177,plain,(
% 33.24/4.53    spl3_40 | ~spl3_4 | ~spl3_16),
% 33.24/4.53    inference(avatar_split_clause,[],[f41527,f386,f66,f44174])).
% 33.24/4.53  fof(f44174,plain,(
% 33.24/4.53    spl3_40 <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 33.24/4.53  fof(f41527,plain,(
% 33.24/4.53    sK1 = k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) | (~spl3_4 | ~spl3_16)),
% 33.24/4.53    inference(forward_demodulation,[],[f41503,f271])).
% 33.24/4.53  fof(f41503,plain,(
% 33.24/4.53    k5_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) | (~spl3_4 | ~spl3_16)),
% 33.24/4.53    inference(superposition,[],[f40236,f388])).
% 33.24/4.53  fof(f31580,plain,(
% 33.24/4.53    spl3_39 | ~spl3_25),
% 33.24/4.53    inference(avatar_split_clause,[],[f5823,f5819,f31577])).
% 33.24/4.53  fof(f31577,plain,(
% 33.24/4.53    spl3_39 <=> k4_xboole_0(sK1,sK2) = k3_xboole_0(k4_xboole_0(sK1,sK2),sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 33.24/4.53  fof(f5819,plain,(
% 33.24/4.53    spl3_25 <=> r1_tarski(k4_xboole_0(sK1,sK2),sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 33.24/4.53  fof(f5823,plain,(
% 33.24/4.53    k4_xboole_0(sK1,sK2) = k3_xboole_0(k4_xboole_0(sK1,sK2),sK1) | ~spl3_25),
% 33.24/4.53    inference(resolution,[],[f5821,f34])).
% 33.24/4.53  fof(f5821,plain,(
% 33.24/4.53    r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~spl3_25),
% 33.24/4.53    inference(avatar_component_clause,[],[f5819])).
% 33.24/4.53  fof(f31575,plain,(
% 33.24/4.53    spl3_38 | ~spl3_24),
% 33.24/4.53    inference(avatar_split_clause,[],[f5817,f5813,f31572])).
% 33.24/4.53  fof(f31572,plain,(
% 33.24/4.53    spl3_38 <=> k4_xboole_0(sK1,sK0) = k3_xboole_0(k4_xboole_0(sK1,sK0),sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 33.24/4.53  fof(f5813,plain,(
% 33.24/4.53    spl3_24 <=> r1_tarski(k4_xboole_0(sK1,sK0),sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 33.24/4.53  fof(f5817,plain,(
% 33.24/4.53    k4_xboole_0(sK1,sK0) = k3_xboole_0(k4_xboole_0(sK1,sK0),sK1) | ~spl3_24),
% 33.24/4.53    inference(resolution,[],[f5815,f34])).
% 33.24/4.53  fof(f5815,plain,(
% 33.24/4.53    r1_tarski(k4_xboole_0(sK1,sK0),sK1) | ~spl3_24),
% 33.24/4.53    inference(avatar_component_clause,[],[f5813])).
% 33.24/4.53  fof(f30515,plain,(
% 33.24/4.53    spl3_37 | ~spl3_15 | ~spl3_18 | ~spl3_21),
% 33.24/4.53    inference(avatar_split_clause,[],[f3135,f561,f525,f348,f30512])).
% 33.24/4.53  fof(f30512,plain,(
% 33.24/4.53    spl3_37 <=> k4_xboole_0(sK1,sK0) = k5_xboole_0(sK0,sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 33.24/4.53  fof(f348,plain,(
% 33.24/4.53    spl3_15 <=> k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK0)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 33.24/4.53  fof(f525,plain,(
% 33.24/4.53    spl3_18 <=> k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 33.24/4.53  fof(f3135,plain,(
% 33.24/4.53    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK0,sK1) | (~spl3_15 | ~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(superposition,[],[f3107,f350])).
% 33.24/4.53  fof(f350,plain,(
% 33.24/4.53    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK0) | ~spl3_15),
% 33.24/4.53    inference(avatar_component_clause,[],[f348])).
% 33.24/4.53  fof(f3107,plain,(
% 33.24/4.53    ( ! [X0] : (k5_xboole_0(X0,sK1) = k5_xboole_0(sK1,X0)) ) | (~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(forward_demodulation,[],[f3088,f563])).
% 33.24/4.53  fof(f3088,plain,(
% 33.24/4.53    ( ! [X0] : (k5_xboole_0(k2_xboole_0(sK0,sK1),X0) = k5_xboole_0(X0,sK1)) ) | (~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(superposition,[],[f2938,f534])).
% 33.24/4.53  fof(f534,plain,(
% 33.24/4.53    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(sK0,sK1),X0)) = X0) ) | ~spl3_18),
% 33.24/4.53    inference(forward_demodulation,[],[f531,f271])).
% 33.24/4.53  fof(f531,plain,(
% 33.24/4.53    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(sK0,sK1),X0))) ) | ~spl3_18),
% 33.24/4.53    inference(superposition,[],[f35,f527])).
% 33.24/4.53  fof(f527,plain,(
% 33.24/4.53    k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)) | ~spl3_18),
% 33.24/4.53    inference(avatar_component_clause,[],[f525])).
% 33.24/4.53  fof(f2938,plain,(
% 33.24/4.53    ( ! [X2] : (k5_xboole_0(k5_xboole_0(sK1,X2),sK1) = X2) ) | (~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(forward_demodulation,[],[f2928,f271])).
% 33.24/4.53  fof(f2928,plain,(
% 33.24/4.53    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(sK1,X2),sK1)) ) | (~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(superposition,[],[f255,f2900])).
% 33.24/4.53  fof(f2900,plain,(
% 33.24/4.53    ( ! [X0] : (sK1 = k5_xboole_0(k5_xboole_0(sK1,X0),X0)) ) | (~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(forward_demodulation,[],[f2874,f563])).
% 33.24/4.53  fof(f2874,plain,(
% 33.24/4.53    ( ! [X0] : (sK1 = k5_xboole_0(k5_xboole_0(k2_xboole_0(sK0,sK1),X0),X0)) ) | (~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(superposition,[],[f2868,f534])).
% 33.24/4.53  fof(f2868,plain,(
% 33.24/4.53    ( ! [X5] : (sK1 = k5_xboole_0(X5,k5_xboole_0(sK1,X5))) ) | (~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(forward_demodulation,[],[f2867,f27])).
% 33.24/4.53  fof(f2867,plain,(
% 33.24/4.53    ( ! [X5] : (k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(X5,k5_xboole_0(sK1,X5))) ) | (~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(forward_demodulation,[],[f2853,f563])).
% 33.24/4.53  fof(f2853,plain,(
% 33.24/4.53    ( ! [X5] : (k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(X5,k5_xboole_0(k2_xboole_0(sK0,sK1),X5))) ) | ~spl3_18),
% 33.24/4.53    inference(superposition,[],[f534,f261])).
% 33.24/4.53  fof(f26189,plain,(
% 33.24/4.53    spl3_36 | ~spl3_13 | ~spl3_18 | ~spl3_21),
% 33.24/4.53    inference(avatar_split_clause,[],[f3093,f561,f525,f175,f26186])).
% 33.24/4.53  fof(f26186,plain,(
% 33.24/4.53    spl3_36 <=> sK2 = k5_xboole_0(k4_xboole_0(sK1,sK2),sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 33.24/4.53  fof(f175,plain,(
% 33.24/4.53    spl3_13 <=> k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK2)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 33.24/4.53  fof(f3093,plain,(
% 33.24/4.53    sK2 = k5_xboole_0(k4_xboole_0(sK1,sK2),sK1) | (~spl3_13 | ~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(superposition,[],[f2938,f177])).
% 33.24/4.53  fof(f177,plain,(
% 33.24/4.53    k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK2) | ~spl3_13),
% 33.24/4.53    inference(avatar_component_clause,[],[f175])).
% 33.24/4.53  fof(f26138,plain,(
% 33.24/4.53    spl3_35 | ~spl3_15 | ~spl3_18 | ~spl3_21),
% 33.24/4.53    inference(avatar_split_clause,[],[f3092,f561,f525,f348,f26135])).
% 33.24/4.53  fof(f26135,plain,(
% 33.24/4.53    spl3_35 <=> sK0 = k5_xboole_0(k4_xboole_0(sK1,sK0),sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 33.24/4.53  fof(f3092,plain,(
% 33.24/4.53    sK0 = k5_xboole_0(k4_xboole_0(sK1,sK0),sK1) | (~spl3_15 | ~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(superposition,[],[f2938,f350])).
% 33.24/4.53  fof(f26093,plain,(
% 33.24/4.53    spl3_34 | ~spl3_13 | ~spl3_18 | ~spl3_21),
% 33.24/4.53    inference(avatar_split_clause,[],[f3063,f561,f525,f175,f26090])).
% 33.24/4.53  fof(f26090,plain,(
% 33.24/4.53    spl3_34 <=> sK2 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 33.24/4.53  fof(f3063,plain,(
% 33.24/4.53    sK2 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | (~spl3_13 | ~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(superposition,[],[f2846,f177])).
% 33.24/4.53  fof(f2846,plain,(
% 33.24/4.53    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = X0) ) | (~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(superposition,[],[f534,f563])).
% 33.24/4.53  fof(f26043,plain,(
% 33.24/4.53    spl3_33 | ~spl3_15 | ~spl3_18 | ~spl3_21),
% 33.24/4.53    inference(avatar_split_clause,[],[f3062,f561,f525,f348,f26040])).
% 33.24/4.53  fof(f26040,plain,(
% 33.24/4.53    spl3_33 <=> sK0 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 33.24/4.53  fof(f3062,plain,(
% 33.24/4.53    sK0 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | (~spl3_15 | ~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(superposition,[],[f2846,f350])).
% 33.24/4.53  fof(f19224,plain,(
% 33.24/4.53    spl3_32 | ~spl3_13 | ~spl3_18 | ~spl3_21),
% 33.24/4.53    inference(avatar_split_clause,[],[f2913,f561,f525,f175,f19221])).
% 33.24/4.53  fof(f2913,plain,(
% 33.24/4.53    sK1 = k5_xboole_0(k4_xboole_0(sK1,sK2),sK2) | (~spl3_13 | ~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(superposition,[],[f2900,f177])).
% 33.24/4.53  fof(f19201,plain,(
% 33.24/4.53    spl3_31 | ~spl3_15 | ~spl3_18 | ~spl3_21),
% 33.24/4.53    inference(avatar_split_clause,[],[f2912,f561,f525,f348,f19198])).
% 33.24/4.53  fof(f2912,plain,(
% 33.24/4.53    sK1 = k5_xboole_0(k4_xboole_0(sK1,sK0),sK0) | (~spl3_15 | ~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(superposition,[],[f2900,f350])).
% 33.24/4.53  fof(f13540,plain,(
% 33.24/4.53    spl3_30 | ~spl3_29),
% 33.24/4.53    inference(avatar_split_clause,[],[f13527,f13510,f13537])).
% 33.24/4.53  fof(f13537,plain,(
% 33.24/4.53    spl3_30 <=> k4_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 33.24/4.53  fof(f13510,plain,(
% 33.24/4.53    spl3_29 <=> sK1 = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 33.24/4.53  fof(f13527,plain,(
% 33.24/4.53    k4_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1) | ~spl3_29),
% 33.24/4.53    inference(forward_demodulation,[],[f13519,f271])).
% 33.24/4.53  fof(f13519,plain,(
% 33.24/4.53    k5_xboole_0(sK2,sK1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) | ~spl3_29),
% 33.24/4.53    inference(superposition,[],[f255,f13512])).
% 33.24/4.53  fof(f13512,plain,(
% 33.24/4.53    sK1 = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~spl3_29),
% 33.24/4.53    inference(avatar_component_clause,[],[f13510])).
% 33.24/4.53  fof(f13513,plain,(
% 33.24/4.53    spl3_29 | ~spl3_13 | ~spl3_18 | ~spl3_21),
% 33.24/4.53    inference(avatar_split_clause,[],[f2878,f561,f525,f175,f13510])).
% 33.24/4.53  fof(f2878,plain,(
% 33.24/4.53    sK1 = k5_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | (~spl3_13 | ~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(superposition,[],[f2868,f177])).
% 33.24/4.53  fof(f13484,plain,(
% 33.24/4.53    spl3_28 | ~spl3_15 | ~spl3_18 | ~spl3_21),
% 33.24/4.53    inference(avatar_split_clause,[],[f2877,f561,f525,f348,f13481])).
% 33.24/4.53  fof(f13481,plain,(
% 33.24/4.53    spl3_28 <=> sK1 = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 33.24/4.53  fof(f2877,plain,(
% 33.24/4.53    sK1 = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | (~spl3_15 | ~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(superposition,[],[f2868,f350])).
% 33.24/4.53  fof(f6060,plain,(
% 33.24/4.53    spl3_27 | ~spl3_13),
% 33.24/4.53    inference(avatar_split_clause,[],[f6031,f175,f6057])).
% 33.24/4.53  fof(f6057,plain,(
% 33.24/4.53    spl3_27 <=> r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 33.24/4.53  fof(f6031,plain,(
% 33.24/4.53    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) | ~spl3_13),
% 33.24/4.53    inference(superposition,[],[f5681,f177])).
% 33.24/4.53  fof(f6055,plain,(
% 33.24/4.53    spl3_26 | ~spl3_15),
% 33.24/4.53    inference(avatar_split_clause,[],[f6030,f348,f6052])).
% 33.24/4.53  fof(f6052,plain,(
% 33.24/4.53    spl3_26 <=> r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 33.24/4.53  fof(f6030,plain,(
% 33.24/4.53    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),sK0) | ~spl3_15),
% 33.24/4.53    inference(superposition,[],[f5681,f350])).
% 33.24/4.53  fof(f5822,plain,(
% 33.24/4.53    spl3_25 | ~spl3_13 | ~spl3_18 | ~spl3_21),
% 33.24/4.53    inference(avatar_split_clause,[],[f5805,f561,f525,f175,f5819])).
% 33.24/4.53  fof(f5805,plain,(
% 33.24/4.53    r1_tarski(k4_xboole_0(sK1,sK2),sK1) | (~spl3_13 | ~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(forward_demodulation,[],[f5789,f645])).
% 33.24/4.53  fof(f645,plain,(
% 33.24/4.53    ( ! [X15,X16] : (k4_xboole_0(X16,X15) = k4_xboole_0(k4_xboole_0(X16,X15),X15)) )),
% 33.24/4.53    inference(forward_demodulation,[],[f636,f27])).
% 33.24/4.53  fof(f636,plain,(
% 33.24/4.53    ( ! [X15,X16] : (k4_xboole_0(k4_xboole_0(X16,X15),X15) = k5_xboole_0(k4_xboole_0(X16,X15),k1_xboole_0)) )),
% 33.24/4.53    inference(superposition,[],[f141,f575])).
% 33.24/4.53  fof(f5789,plain,(
% 33.24/4.53    r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK2),sK2),sK1) | (~spl3_13 | ~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(superposition,[],[f5662,f177])).
% 33.24/4.53  fof(f5662,plain,(
% 33.24/4.53    ( ! [X20] : (r1_tarski(k4_xboole_0(k5_xboole_0(sK1,X20),X20),sK1)) ) | (~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(superposition,[],[f5595,f2900])).
% 33.24/4.53  fof(f5816,plain,(
% 33.24/4.53    spl3_24 | ~spl3_15 | ~spl3_18 | ~spl3_21),
% 33.24/4.53    inference(avatar_split_clause,[],[f5804,f561,f525,f348,f5813])).
% 33.24/4.53  fof(f5804,plain,(
% 33.24/4.53    r1_tarski(k4_xboole_0(sK1,sK0),sK1) | (~spl3_15 | ~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(forward_demodulation,[],[f5788,f645])).
% 33.24/4.53  fof(f5788,plain,(
% 33.24/4.53    r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK0),sK0),sK1) | (~spl3_15 | ~spl3_18 | ~spl3_21)),
% 33.24/4.53    inference(superposition,[],[f5662,f350])).
% 33.24/4.53  fof(f616,plain,(
% 33.24/4.53    spl3_23 | ~spl3_22),
% 33.24/4.53    inference(avatar_split_clause,[],[f603,f599,f613])).
% 33.24/4.53  fof(f599,plain,(
% 33.24/4.53    spl3_22 <=> sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK2,sK1))),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 33.24/4.53  fof(f603,plain,(
% 33.24/4.53    sK1 = k2_xboole_0(sK2,sK1) | ~spl3_22),
% 33.24/4.53    inference(superposition,[],[f601,f271])).
% 33.24/4.53  fof(f601,plain,(
% 33.24/4.53    sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK2,sK1)) | ~spl3_22),
% 33.24/4.53    inference(avatar_component_clause,[],[f599])).
% 33.24/4.53  fof(f602,plain,(
% 33.24/4.53    spl3_22 | ~spl3_19),
% 33.24/4.53    inference(avatar_split_clause,[],[f549,f536,f599])).
% 33.24/4.53  fof(f536,plain,(
% 33.24/4.53    spl3_19 <=> k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(sK2,sK1))),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 33.24/4.53  fof(f549,plain,(
% 33.24/4.53    sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK2,sK1)) | ~spl3_19),
% 33.24/4.53    inference(forward_demodulation,[],[f546,f27])).
% 33.24/4.53  fof(f546,plain,(
% 33.24/4.53    k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK2,sK1)) | ~spl3_19),
% 33.24/4.53    inference(superposition,[],[f255,f538])).
% 33.24/4.53  fof(f538,plain,(
% 33.24/4.53    k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(sK2,sK1)) | ~spl3_19),
% 33.24/4.53    inference(avatar_component_clause,[],[f536])).
% 33.24/4.53  fof(f564,plain,(
% 33.24/4.53    spl3_21 | ~spl3_20),
% 33.24/4.53    inference(avatar_split_clause,[],[f551,f541,f561])).
% 33.24/4.53  fof(f541,plain,(
% 33.24/4.53    spl3_20 <=> sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 33.24/4.53  fof(f551,plain,(
% 33.24/4.53    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_20),
% 33.24/4.53    inference(superposition,[],[f543,f271])).
% 33.24/4.53  fof(f543,plain,(
% 33.24/4.53    sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) | ~spl3_20),
% 33.24/4.53    inference(avatar_component_clause,[],[f541])).
% 33.24/4.53  fof(f544,plain,(
% 33.24/4.53    spl3_20 | ~spl3_18),
% 33.24/4.53    inference(avatar_split_clause,[],[f533,f525,f541])).
% 33.24/4.53  fof(f533,plain,(
% 33.24/4.53    sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) | ~spl3_18),
% 33.24/4.53    inference(forward_demodulation,[],[f530,f27])).
% 33.24/4.53  fof(f530,plain,(
% 33.24/4.53    k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) | ~spl3_18),
% 33.24/4.53    inference(superposition,[],[f255,f527])).
% 33.24/4.53  fof(f539,plain,(
% 33.24/4.53    spl3_19 | ~spl3_13),
% 33.24/4.53    inference(avatar_split_clause,[],[f504,f175,f536])).
% 33.24/4.53  fof(f504,plain,(
% 33.24/4.53    k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(sK2,sK1)) | ~spl3_13),
% 33.24/4.53    inference(forward_demodulation,[],[f477,f31])).
% 33.24/4.53  fof(f477,plain,(
% 33.24/4.53    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,k4_xboole_0(sK1,sK2))) | ~spl3_13),
% 33.24/4.53    inference(superposition,[],[f261,f177])).
% 33.24/4.53  fof(f528,plain,(
% 33.24/4.53    spl3_18 | ~spl3_15),
% 33.24/4.53    inference(avatar_split_clause,[],[f505,f348,f525])).
% 33.24/4.53  fof(f505,plain,(
% 33.24/4.53    k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)) | ~spl3_15),
% 33.24/4.53    inference(forward_demodulation,[],[f478,f31])).
% 33.24/4.53  fof(f478,plain,(
% 33.24/4.53    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) | ~spl3_15),
% 33.24/4.53    inference(superposition,[],[f261,f350])).
% 33.24/4.53  fof(f428,plain,(
% 33.24/4.53    spl3_17 | ~spl3_15),
% 33.24/4.53    inference(avatar_split_clause,[],[f416,f348,f425])).
% 33.24/4.53  fof(f416,plain,(
% 33.24/4.53    sK0 = k3_xboole_0(sK1,sK0) | ~spl3_15),
% 33.24/4.53    inference(forward_demodulation,[],[f415,f271])).
% 33.24/4.53  fof(f415,plain,(
% 33.24/4.53    k3_xboole_0(sK1,sK0) = k5_xboole_0(k1_xboole_0,sK0) | ~spl3_15),
% 33.24/4.53    inference(forward_demodulation,[],[f402,f407])).
% 33.24/4.53  fof(f402,plain,(
% 33.24/4.53    k5_xboole_0(k1_xboole_0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | ~spl3_15),
% 33.24/4.53    inference(superposition,[],[f255,f350])).
% 33.24/4.53  fof(f389,plain,(
% 33.24/4.53    spl3_16 | ~spl3_4),
% 33.24/4.53    inference(avatar_split_clause,[],[f359,f66,f386])).
% 33.24/4.53  fof(f359,plain,(
% 33.24/4.53    sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f205,f68])).
% 33.24/4.53  fof(f205,plain,(
% 33.24/4.53    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X2,X1),k4_xboole_0(X1,X2)) = X1) )),
% 33.24/4.53    inference(superposition,[],[f33,f29])).
% 33.24/4.53  fof(f351,plain,(
% 33.24/4.53    spl3_15 | ~spl3_4),
% 33.24/4.53    inference(avatar_split_clause,[],[f333,f66,f348])).
% 33.24/4.53  fof(f333,plain,(
% 33.24/4.53    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK0) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f141,f68])).
% 33.24/4.53  fof(f293,plain,(
% 33.24/4.53    spl3_14 | ~spl3_8),
% 33.24/4.53    inference(avatar_split_clause,[],[f211,f94,f290])).
% 33.24/4.53  fof(f211,plain,(
% 33.24/4.53    sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~spl3_8),
% 33.24/4.53    inference(superposition,[],[f33,f96])).
% 33.24/4.53  fof(f178,plain,(
% 33.24/4.53    spl3_13 | ~spl3_8),
% 33.24/4.53    inference(avatar_split_clause,[],[f147,f94,f175])).
% 33.24/4.53  fof(f147,plain,(
% 33.24/4.53    k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,sK2) | ~spl3_8),
% 33.24/4.53    inference(superposition,[],[f32,f96])).
% 33.24/4.53  fof(f164,plain,(
% 33.24/4.53    spl3_12 | ~spl3_5),
% 33.24/4.53    inference(avatar_split_clause,[],[f154,f71,f161])).
% 33.24/4.53  fof(f161,plain,(
% 33.24/4.53    spl3_12 <=> k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 33.24/4.53  fof(f154,plain,(
% 33.24/4.53    k1_xboole_0 = k4_xboole_0(sK2,sK1) | ~spl3_5),
% 33.24/4.53    inference(forward_demodulation,[],[f148,f26])).
% 33.24/4.53  fof(f148,plain,(
% 33.24/4.53    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,sK2) | ~spl3_5),
% 33.24/4.53    inference(superposition,[],[f32,f73])).
% 33.24/4.53  fof(f159,plain,(
% 33.24/4.53    spl3_11 | ~spl3_4),
% 33.24/4.53    inference(avatar_split_clause,[],[f153,f66,f156])).
% 33.24/4.53  fof(f156,plain,(
% 33.24/4.53    spl3_11 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 33.24/4.53  fof(f153,plain,(
% 33.24/4.53    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_4),
% 33.24/4.53    inference(forward_demodulation,[],[f146,f26])).
% 33.24/4.53  fof(f146,plain,(
% 33.24/4.53    k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,sK0) | ~spl3_4),
% 33.24/4.53    inference(superposition,[],[f32,f68])).
% 33.24/4.53  fof(f107,plain,(
% 33.24/4.53    spl3_10 | ~spl3_5),
% 33.24/4.53    inference(avatar_split_clause,[],[f80,f71,f104])).
% 33.24/4.53  fof(f104,plain,(
% 33.24/4.53    spl3_10 <=> sK2 = k2_xboole_0(sK2,sK2)),
% 33.24/4.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 33.24/4.53  fof(f80,plain,(
% 33.24/4.53    sK2 = k2_xboole_0(sK2,sK2) | ~spl3_5),
% 33.24/4.53    inference(superposition,[],[f30,f73])).
% 33.24/4.54  fof(f102,plain,(
% 33.24/4.54    spl3_9 | ~spl3_5),
% 33.24/4.54    inference(avatar_split_clause,[],[f79,f71,f99])).
% 33.24/4.54  fof(f99,plain,(
% 33.24/4.54    spl3_9 <=> sK1 = k2_xboole_0(sK1,sK2)),
% 33.24/4.54    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 33.24/4.54  fof(f79,plain,(
% 33.24/4.54    sK1 = k2_xboole_0(sK1,sK2) | ~spl3_5),
% 33.24/4.54    inference(superposition,[],[f54,f73])).
% 33.24/4.54  fof(f97,plain,(
% 33.24/4.54    spl3_8 | ~spl3_5),
% 33.24/4.54    inference(avatar_split_clause,[],[f77,f71,f94])).
% 33.24/4.54  fof(f77,plain,(
% 33.24/4.54    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_5),
% 33.24/4.54    inference(superposition,[],[f73,f29])).
% 33.24/4.54  fof(f92,plain,(
% 33.24/4.54    spl3_7 | ~spl3_4),
% 33.24/4.54    inference(avatar_split_clause,[],[f76,f66,f89])).
% 33.24/4.54  fof(f89,plain,(
% 33.24/4.54    spl3_7 <=> sK0 = k2_xboole_0(sK0,sK0)),
% 33.24/4.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 33.24/4.54  fof(f76,plain,(
% 33.24/4.54    sK0 = k2_xboole_0(sK0,sK0) | ~spl3_4),
% 33.24/4.54    inference(superposition,[],[f30,f68])).
% 33.24/4.54  fof(f87,plain,(
% 33.24/4.54    spl3_6 | ~spl3_4),
% 33.24/4.54    inference(avatar_split_clause,[],[f75,f66,f84])).
% 33.24/4.54  fof(f84,plain,(
% 33.24/4.54    spl3_6 <=> sK1 = k2_xboole_0(sK1,sK0)),
% 33.24/4.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 33.24/4.54  fof(f75,plain,(
% 33.24/4.54    sK1 = k2_xboole_0(sK1,sK0) | ~spl3_4),
% 33.24/4.54    inference(superposition,[],[f54,f68])).
% 33.24/4.54  fof(f74,plain,(
% 33.24/4.54    spl3_5 | ~spl3_2),
% 33.24/4.54    inference(avatar_split_clause,[],[f64,f45,f71])).
% 33.24/4.54  fof(f45,plain,(
% 33.24/4.54    spl3_2 <=> r1_tarski(sK2,sK1)),
% 33.24/4.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 33.24/4.54  fof(f64,plain,(
% 33.24/4.54    sK2 = k3_xboole_0(sK2,sK1) | ~spl3_2),
% 33.24/4.54    inference(resolution,[],[f34,f47])).
% 33.24/4.54  fof(f47,plain,(
% 33.24/4.54    r1_tarski(sK2,sK1) | ~spl3_2),
% 33.24/4.54    inference(avatar_component_clause,[],[f45])).
% 33.24/4.54  fof(f69,plain,(
% 33.24/4.54    spl3_4 | ~spl3_1),
% 33.24/4.54    inference(avatar_split_clause,[],[f63,f40,f66])).
% 33.24/4.54  fof(f40,plain,(
% 33.24/4.54    spl3_1 <=> r1_tarski(sK0,sK1)),
% 33.24/4.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 33.24/4.54  fof(f63,plain,(
% 33.24/4.54    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_1),
% 33.24/4.54    inference(resolution,[],[f34,f42])).
% 33.24/4.54  fof(f42,plain,(
% 33.24/4.54    r1_tarski(sK0,sK1) | ~spl3_1),
% 33.24/4.54    inference(avatar_component_clause,[],[f40])).
% 33.24/4.54  fof(f53,plain,(
% 33.24/4.54    ~spl3_3),
% 33.24/4.54    inference(avatar_split_clause,[],[f24,f50])).
% 33.24/4.54  fof(f24,plain,(
% 33.24/4.54    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 33.24/4.54    inference(cnf_transformation,[],[f21])).
% 33.24/4.54  fof(f21,plain,(
% 33.24/4.54    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1)),
% 33.24/4.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20])).
% 33.24/4.54  fof(f20,plain,(
% 33.24/4.54    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => (~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1))),
% 33.24/4.54    introduced(choice_axiom,[])).
% 33.24/4.54  fof(f18,plain,(
% 33.24/4.54    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 33.24/4.54    inference(flattening,[],[f17])).
% 33.24/4.54  fof(f17,plain,(
% 33.24/4.54    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & (r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 33.24/4.54    inference(ennf_transformation,[],[f16])).
% 33.24/4.54  fof(f16,negated_conjecture,(
% 33.24/4.54    ~! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 33.24/4.54    inference(negated_conjecture,[],[f15])).
% 33.24/4.54  fof(f15,conjecture,(
% 33.24/4.54    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 33.24/4.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).
% 33.24/4.54  fof(f48,plain,(
% 33.24/4.54    spl3_2),
% 33.24/4.54    inference(avatar_split_clause,[],[f23,f45])).
% 33.24/4.54  fof(f23,plain,(
% 33.24/4.54    r1_tarski(sK2,sK1)),
% 33.24/4.54    inference(cnf_transformation,[],[f21])).
% 33.24/4.54  fof(f43,plain,(
% 33.24/4.54    spl3_1),
% 33.24/4.54    inference(avatar_split_clause,[],[f22,f40])).
% 33.24/4.54  fof(f22,plain,(
% 33.24/4.54    r1_tarski(sK0,sK1)),
% 33.24/4.54    inference(cnf_transformation,[],[f21])).
% 33.24/4.54  % SZS output end Proof for theBenchmark
% 33.24/4.54  % (20901)------------------------------
% 33.24/4.54  % (20901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 33.24/4.54  % (20901)Termination reason: Refutation
% 33.24/4.54  
% 33.24/4.54  % (20901)Memory used [KB]: 72791
% 33.24/4.54  % (20901)Time elapsed: 4.093 s
% 33.24/4.54  % (20901)------------------------------
% 33.24/4.54  % (20901)------------------------------
% 33.24/4.56  % (20900)Success in time 4.195 s
%------------------------------------------------------------------------------
