%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 285 expanded)
%              Number of leaves         :   22 ( 100 expanded)
%              Depth                    :   19
%              Number of atoms          :  141 ( 383 expanded)
%              Number of equality atoms :   74 ( 269 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f213,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f111,f112,f163,f211])).

fof(f211,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl4_7 ),
    inference(trivial_inequality_removal,[],[f196])).

fof(f196,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2)
    | spl4_7 ),
    inference(backward_demodulation,[],[f162,f189])).

fof(f189,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f178,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f178,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f95,f76])).

fof(f76,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f39,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f95,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f73,f89])).

fof(f89,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f82,f30])).

fof(f82,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f73,f29])).

fof(f73,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f39,f29])).

fof(f162,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl4_7
  <=> k2_zfmisc_1(sK0,sK2) = k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f163,plain,
    ( ~ spl4_7
    | spl4_1
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f158,f107,f102,f59,f160])).

fof(f59,plain,
    ( spl4_1
  <=> k2_zfmisc_1(sK0,sK2) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f102,plain,
    ( spl4_4
  <=> sK1 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f107,plain,
    ( spl4_5
  <=> sK3 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f158,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f157,f30])).

fof(f157,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f156,f29])).

fof(f156,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f155,f104])).

fof(f104,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f155,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))
    | spl4_1
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f154,f109])).

fof(f109,plain,
    ( sK3 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f154,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)))))
    | spl4_1 ),
    inference(forward_demodulation,[],[f140,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f33,f50,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f40,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

% (31530)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% (31536)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% (31540)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% (31545)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% (31535)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f140,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)))))
    | spl4_1 ),
    inference(superposition,[],[f61,f134])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))) ),
    inference(forward_demodulation,[],[f133,f39])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))) ),
    inference(forward_demodulation,[],[f57,f39])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) ),
    inference(definition_unfolding,[],[f41,f51,f51,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f36,f50])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f61,plain,
    ( k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f112,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f100,f69,f102])).

fof(f69,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f100,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl4_3 ),
    inference(resolution,[],[f56,f71])).

fof(f71,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f37,f50])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f111,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f99,f64,f107])).

fof(f64,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f99,plain,
    ( sK3 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl4_2 ),
    inference(resolution,[],[f56,f66])).

fof(f66,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f72,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f26,f69])).

fof(f26,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).

fof(f67,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f52,f59])).

fof(f52,plain,(
    k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) ),
    inference(definition_unfolding,[],[f28,f51])).

fof(f28,plain,(
    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:07:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (31529)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (31542)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (31539)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (31544)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  % (31525)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (31527)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (31533)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (31538)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (31532)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (31534)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (31532)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f62,f67,f72,f111,f112,f163,f211])).
% 0.22/0.49  fof(f211,plain,(
% 0.22/0.49    spl4_7),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f210])).
% 0.22/0.49  fof(f210,plain,(
% 0.22/0.49    $false | spl4_7),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f196])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2) | spl4_7),
% 0.22/0.49    inference(backward_demodulation,[],[f162,f189])).
% 0.22/0.49  fof(f189,plain,(
% 0.22/0.49    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 0.22/0.49    inference(forward_demodulation,[],[f178,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 0.22/0.49    inference(superposition,[],[f95,f76])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 0.22/0.49    inference(superposition,[],[f39,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.22/0.49    inference(backward_demodulation,[],[f73,f89])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.49    inference(forward_demodulation,[],[f82,f30])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.49    inference(superposition,[],[f73,f29])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 0.22/0.49    inference(superposition,[],[f39,f29])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) | spl4_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f160])).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    spl4_7 <=> k2_zfmisc_1(sK0,sK2) = k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    ~spl4_7 | spl4_1 | ~spl4_4 | ~spl4_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f158,f107,f102,f59,f160])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    spl4_1 <=> k2_zfmisc_1(sK0,sK2) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl4_4 <=> sK1 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    spl4_5 <=> sK3 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) | (spl4_1 | ~spl4_4 | ~spl4_5)),
% 0.22/0.49    inference(forward_demodulation,[],[f157,f30])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) | (spl4_1 | ~spl4_4 | ~spl4_5)),
% 0.22/0.49    inference(forward_demodulation,[],[f156,f29])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) | (spl4_1 | ~spl4_4 | ~spl4_5)),
% 0.22/0.49    inference(forward_demodulation,[],[f155,f104])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    sK1 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl4_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f102])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) | (spl4_1 | ~spl4_5)),
% 0.22/0.49    inference(forward_demodulation,[],[f154,f109])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    sK3 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | ~spl4_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f107])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))))) | spl4_1),
% 0.22/0.49    inference(forward_demodulation,[],[f140,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f33,f50,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f34,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f35,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f38,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f40,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f42,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f43,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.50  % (31530)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (31536)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (31540)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (31545)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (31535)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2))))) | spl4_1),
% 0.22/0.51    inference(superposition,[],[f61,f134])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f133,f39])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f57,f39])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f41,f51,f51,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f36,f50])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) | spl4_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f59])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    spl4_4 | ~spl4_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f100,f69,f102])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    spl4_3 <=> r1_tarski(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    sK1 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl4_3),
% 0.22/0.51    inference(resolution,[],[f56,f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    r1_tarski(sK0,sK1) | ~spl4_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f69])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1) )),
% 0.22/0.51    inference(definition_unfolding,[],[f37,f50])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    spl4_5 | ~spl4_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f99,f64,f107])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    spl4_2 <=> r1_tarski(sK2,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    sK3 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | ~spl4_2),
% 0.22/0.51    inference(resolution,[],[f56,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    r1_tarski(sK2,sK3) | ~spl4_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f64])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    spl4_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f26,f69])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    r1_tarski(sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 0.22/0.51    inference(negated_conjecture,[],[f17])).
% 0.22/0.51  fof(f17,conjecture,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    spl4_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f27,f64])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    r1_tarski(sK2,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ~spl4_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f52,f59])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))),
% 0.22/0.51    inference(definition_unfolding,[],[f28,f51])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (31532)------------------------------
% 0.22/0.51  % (31532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (31532)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (31532)Memory used [KB]: 6268
% 0.22/0.51  % (31532)Time elapsed: 0.069 s
% 0.22/0.51  % (31532)------------------------------
% 0.22/0.51  % (31532)------------------------------
% 0.22/0.51  % (31523)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (31524)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  % (31515)Success in time 0.139 s
%------------------------------------------------------------------------------
