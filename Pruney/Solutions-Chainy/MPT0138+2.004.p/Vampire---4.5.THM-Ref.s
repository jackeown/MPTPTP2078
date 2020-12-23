%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 111 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 ( 126 expanded)
%              Number of equality atoms :   45 ( 107 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f323,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f197,f321])).

fof(f321,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | spl6_2 ),
    inference(subsumption_resolution,[],[f319,f160])).

fof(f160,plain,(
    ! [X26,X24,X23,X27,X25,X22] : k2_xboole_0(k1_enumset1(X27,X22,X23),k1_enumset1(X24,X25,X26)) = k2_xboole_0(k1_tarski(X27),k2_xboole_0(k1_tarski(X24),k2_xboole_0(k1_tarski(X25),k1_enumset1(X26,X22,X23)))) ),
    inference(forward_demodulation,[],[f159,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f159,plain,(
    ! [X26,X24,X23,X27,X25,X22] : k2_xboole_0(k1_enumset1(X27,X22,X23),k1_enumset1(X24,X25,X26)) = k2_xboole_0(k1_tarski(X27),k2_xboole_0(k1_tarski(X24),k2_xboole_0(k1_enumset1(X25,X26,X22),k1_tarski(X23)))) ),
    inference(forward_demodulation,[],[f131,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_tarski(X3),X4)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_enumset1(X1,X2,X3),X4)) ),
    inference(forward_demodulation,[],[f40,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_tarski(X3),X4)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)),X4) ),
    inference(superposition,[],[f17,f26])).

fof(f131,plain,(
    ! [X26,X24,X23,X27,X25,X22] : k2_xboole_0(k1_enumset1(X27,X22,X23),k1_enumset1(X24,X25,X26)) = k2_xboole_0(k1_tarski(X27),k2_xboole_0(k1_enumset1(X24,X25,X26),k2_xboole_0(k1_tarski(X22),k1_tarski(X23)))) ),
    inference(superposition,[],[f27,f32])).

fof(f32,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f17,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_enumset1(X3,X4,X5)))) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_enumset1(X3,X4,X5)))) ),
    inference(definition_unfolding,[],[f21,f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))) ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_enumset1)).

fof(f319,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_enumset1(sK5,sK1,sK2))))
    | spl6_2 ),
    inference(forward_demodulation,[],[f318,f103])).

fof(f103,plain,(
    ! [X30,X33,X31,X29,X32] : k2_xboole_0(k1_tarski(X32),k2_xboole_0(X33,k1_enumset1(X29,X30,X31))) = k2_xboole_0(X33,k2_xboole_0(k1_tarski(X29),k1_enumset1(X30,X31,X32))) ),
    inference(superposition,[],[f32,f26])).

fof(f318,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k1_enumset1(sK1,sK2,sK3))))
    | spl6_2 ),
    inference(forward_demodulation,[],[f317,f32])).

fof(f317,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK4))))
    | spl6_2 ),
    inference(forward_demodulation,[],[f297,f32])).

fof(f297,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5))
    | spl6_2 ),
    inference(superposition,[],[f196,f32])).

fof(f196,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl6_2
  <=> k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) = k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f197,plain,
    ( ~ spl6_2
    | spl6_1 ),
    inference(avatar_split_clause,[],[f50,f45,f194])).

fof(f45,plain,
    ( spl6_1
  <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) = k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f50,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)))
    | spl6_1 ),
    inference(superposition,[],[f47,f15])).

fof(f47,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f48,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f28,f45])).

fof(f28,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
    inference(backward_demodulation,[],[f25,f27])).

fof(f25,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_enumset1(sK3,sK4,sK5)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) ),
    inference(definition_unfolding,[],[f14,f24,f18,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f14,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n003.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 20:24:27 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.42  % (10012)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (10013)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (10011)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (10008)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (10005)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (10004)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (10001)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.52  % (10014)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (10011)Refutation not found, incomplete strategy% (10011)------------------------------
% 0.21/0.52  % (10011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10011)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10011)Memory used [KB]: 10618
% 0.21/0.52  % (10011)Time elapsed: 0.082 s
% 0.21/0.52  % (10011)------------------------------
% 0.21/0.52  % (10011)------------------------------
% 0.21/0.52  % (10000)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.52  % (10010)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (10003)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.52  % (10009)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.53  % (10002)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.53  % (10015)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.53  % (10007)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.53  % (10016)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.54  % (10006)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (10017)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.57  % (10015)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f323,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f48,f197,f321])).
% 0.21/0.57  fof(f321,plain,(
% 0.21/0.57    spl6_2),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f320])).
% 0.21/0.57  fof(f320,plain,(
% 0.21/0.57    $false | spl6_2),
% 0.21/0.57    inference(subsumption_resolution,[],[f319,f160])).
% 0.21/0.57  fof(f160,plain,(
% 0.21/0.57    ( ! [X26,X24,X23,X27,X25,X22] : (k2_xboole_0(k1_enumset1(X27,X22,X23),k1_enumset1(X24,X25,X26)) = k2_xboole_0(k1_tarski(X27),k2_xboole_0(k1_tarski(X24),k2_xboole_0(k1_tarski(X25),k1_enumset1(X26,X22,X23))))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f159,f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f19,f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.57  fof(f159,plain,(
% 0.21/0.57    ( ! [X26,X24,X23,X27,X25,X22] : (k2_xboole_0(k1_enumset1(X27,X22,X23),k1_enumset1(X24,X25,X26)) = k2_xboole_0(k1_tarski(X27),k2_xboole_0(k1_tarski(X24),k2_xboole_0(k1_enumset1(X25,X26,X22),k1_tarski(X23))))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f131,f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_tarski(X3),X4)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_enumset1(X1,X2,X3),X4))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f40,f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_xboole_0(k1_tarski(X3),X4)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)),X4)) )),
% 0.21/0.57    inference(superposition,[],[f17,f26])).
% 0.21/0.57  fof(f131,plain,(
% 0.21/0.57    ( ! [X26,X24,X23,X27,X25,X22] : (k2_xboole_0(k1_enumset1(X27,X22,X23),k1_enumset1(X24,X25,X26)) = k2_xboole_0(k1_tarski(X27),k2_xboole_0(k1_enumset1(X24,X25,X26),k2_xboole_0(k1_tarski(X22),k1_tarski(X23))))) )),
% 0.21/0.57    inference(superposition,[],[f27,f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4))) )),
% 0.21/0.57    inference(superposition,[],[f17,f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_enumset1(X3,X4,X5))))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f22,f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_enumset1(X3,X4,X5))))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f21,f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4)))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f20,f18])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_enumset1)).
% 0.21/0.57  fof(f319,plain,(
% 0.21/0.57    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_enumset1(sK5,sK1,sK2)))) | spl6_2),
% 0.21/0.57    inference(forward_demodulation,[],[f318,f103])).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    ( ! [X30,X33,X31,X29,X32] : (k2_xboole_0(k1_tarski(X32),k2_xboole_0(X33,k1_enumset1(X29,X30,X31))) = k2_xboole_0(X33,k2_xboole_0(k1_tarski(X29),k1_enumset1(X30,X31,X32)))) )),
% 0.21/0.57    inference(superposition,[],[f32,f26])).
% 0.21/0.57  fof(f318,plain,(
% 0.21/0.57    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k1_enumset1(sK1,sK2,sK3)))) | spl6_2),
% 0.21/0.57    inference(forward_demodulation,[],[f317,f32])).
% 0.21/0.57  fof(f317,plain,(
% 0.21/0.57    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK4)))) | spl6_2),
% 0.21/0.57    inference(forward_demodulation,[],[f297,f32])).
% 0.21/0.57  fof(f297,plain,(
% 0.21/0.57    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) | spl6_2),
% 0.21/0.57    inference(superposition,[],[f196,f32])).
% 0.21/0.57  fof(f196,plain,(
% 0.21/0.57    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3))) | spl6_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f194])).
% 0.21/0.57  fof(f194,plain,(
% 0.21/0.57    spl6_2 <=> k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) = k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.57  fof(f197,plain,(
% 0.21/0.57    ~spl6_2 | spl6_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f50,f45,f194])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    spl6_1 <=> k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) = k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3))) | spl6_1),
% 0.21/0.57    inference(superposition,[],[f47,f15])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) | spl6_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f45])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ~spl6_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f28,f45])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5))),
% 0.21/0.57    inference(backward_demodulation,[],[f25,f27])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_enumset1(sK3,sK4,sK5)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),
% 0.21/0.57    inference(definition_unfolding,[],[f14,f24,f18,f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5))),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.21/0.57    inference(negated_conjecture,[],[f9])).
% 0.21/0.57  fof(f9,conjecture,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (10015)------------------------------
% 0.21/0.57  % (10015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (10015)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (10015)Memory used [KB]: 11129
% 0.21/0.57  % (10015)Time elapsed: 0.143 s
% 0.21/0.57  % (10015)------------------------------
% 0.21/0.57  % (10015)------------------------------
% 0.21/0.57  % (9999)Success in time 0.215 s
%------------------------------------------------------------------------------
