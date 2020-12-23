%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 (1812 expanded)
%              Number of leaves         :   12 ( 596 expanded)
%              Depth                    :   21
%              Number of atoms          :   72 (1813 expanded)
%              Number of equality atoms :   71 (1812 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f441,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f440])).

fof(f440,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) ),
    inference(backward_demodulation,[],[f34,f439])).

fof(f439,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) ),
    inference(backward_demodulation,[],[f332,f427])).

fof(f427,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f415,f415])).

fof(f415,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f404,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f36,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f37,f35])).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f19,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f37,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f22,f27])).

fof(f22,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f404,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f338,f343])).

fof(f343,plain,(
    ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f74,f330])).

fof(f330,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f329,f44])).

fof(f329,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f319,f40])).

fof(f319,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f81,f272])).

fof(f272,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f269,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f32,f37])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f269,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f115,f251])).

fof(f251,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f225,f81])).

fof(f225,plain,(
    ! [X16] : k5_xboole_0(k1_xboole_0,X16) = X16 ),
    inference(forward_demodulation,[],[f224,f216])).

fof(f216,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X2,k1_xboole_0),k1_xboole_0)) = X2 ),
    inference(forward_demodulation,[],[f198,f44])).

fof(f198,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X2,k1_xboole_0),k1_xboole_0)) ),
    inference(superposition,[],[f76,f67])).

fof(f76,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)) ),
    inference(superposition,[],[f29,f67])).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f224,plain,(
    ! [X16] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X16,k1_xboole_0),k1_xboole_0))) = X16 ),
    inference(forward_demodulation,[],[f207,f44])).

fof(f207,plain,(
    ! [X16] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X16,k1_xboole_0),k1_xboole_0))) = k5_xboole_0(X16,k1_xboole_0) ),
    inference(superposition,[],[f76,f144])).

fof(f144,plain,(
    ! [X7] : k1_xboole_0 = k5_xboole_0(X7,k5_xboole_0(k1_xboole_0,k4_xboole_0(X7,k1_xboole_0))) ),
    inference(superposition,[],[f74,f44])).

fof(f115,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)),k1_xboole_0)) ),
    inference(superposition,[],[f103,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f25,f25])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f103,plain,(
    ! [X3] : k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(k1_xboole_0,X3),k1_xboole_0)) = X3 ),
    inference(forward_demodulation,[],[f95,f44])).

fof(f95,plain,(
    ! [X3] : k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(k1_xboole_0,X3),k1_xboole_0)) = k5_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f49,f67])).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) ),
    inference(superposition,[],[f29,f35])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f32,f38])).

fof(f74,plain,(
    ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X1,X2),k1_xboole_0))) ),
    inference(superposition,[],[f67,f29])).

fof(f338,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(backward_demodulation,[],[f234,f330])).

fof(f234,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,k1_xboole_0),X3)) = X3 ),
    inference(forward_demodulation,[],[f227,f225])).

fof(f227,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(X2,k1_xboole_0),X3))) = X3 ),
    inference(backward_demodulation,[],[f193,f225])).

fof(f193,plain,(
    ! [X2,X3] : k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(X2,k1_xboole_0),X3))) ),
    inference(forward_demodulation,[],[f183,f29])).

fof(f183,plain,(
    ! [X2,X3] : k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X2,k1_xboole_0)),X3)) ),
    inference(superposition,[],[f29,f144])).

fof(f332,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) ),
    inference(backward_demodulation,[],[f128,f330])).

fof(f128,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f81,f37])).

fof(f34,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k1_tarski(sK0))) ),
    inference(definition_unfolding,[],[f18,f30,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f28,f27,f30])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f24,f27])).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f18,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:57:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (3572)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (3573)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (3573)Refutation not found, incomplete strategy% (3573)------------------------------
% 0.21/0.46  % (3573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (3573)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (3573)Memory used [KB]: 10490
% 0.21/0.46  % (3573)Time elapsed: 0.046 s
% 0.21/0.46  % (3573)------------------------------
% 0.21/0.46  % (3573)------------------------------
% 0.21/0.46  % (3576)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (3567)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (3565)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (3568)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (3575)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (3576)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f441,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f440])).
% 0.21/0.48  fof(f440,plain,(
% 0.21/0.48    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),
% 0.21/0.48    inference(backward_demodulation,[],[f34,f439])).
% 0.21/0.48  fof(f439,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f332,f427])).
% 0.21/0.48  fof(f427,plain,(
% 0.21/0.48    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 0.21/0.48    inference(superposition,[],[f415,f415])).
% 0.21/0.48  fof(f415,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 0.21/0.48    inference(forward_demodulation,[],[f404,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(backward_demodulation,[],[f36,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.48    inference(superposition,[],[f37,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f19,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f22,f27])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f21,f27])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.48    inference(rectify,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.48  fof(f404,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(superposition,[],[f338,f343])).
% 0.21/0.48  fof(f343,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) )),
% 0.21/0.48    inference(backward_demodulation,[],[f74,f330])).
% 0.21/0.48  fof(f330,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(forward_demodulation,[],[f329,f44])).
% 0.21/0.48  fof(f329,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f319,f40])).
% 0.21/0.48  fof(f319,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 0.21/0.48    inference(superposition,[],[f81,f272])).
% 0.21/0.48  fof(f272,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f269,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.48    inference(superposition,[],[f32,f37])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f26,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.48  fof(f269,plain,(
% 0.21/0.48    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),k1_xboole_0))) )),
% 0.21/0.48    inference(backward_demodulation,[],[f115,f251])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    ( ! [X2] : (k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))) )),
% 0.21/0.48    inference(superposition,[],[f225,f81])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    ( ! [X16] : (k5_xboole_0(k1_xboole_0,X16) = X16) )),
% 0.21/0.48    inference(forward_demodulation,[],[f224,f216])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    ( ! [X2] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X2,k1_xboole_0),k1_xboole_0)) = X2) )),
% 0.21/0.48    inference(forward_demodulation,[],[f198,f44])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X2,k1_xboole_0),k1_xboole_0))) )),
% 0.21/0.48    inference(superposition,[],[f76,f67])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1))) )),
% 0.21/0.48    inference(superposition,[],[f29,f67])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.48  fof(f224,plain,(
% 0.21/0.48    ( ! [X16] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X16,k1_xboole_0),k1_xboole_0))) = X16) )),
% 0.21/0.48    inference(forward_demodulation,[],[f207,f44])).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    ( ! [X16] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X16,k1_xboole_0),k1_xboole_0))) = k5_xboole_0(X16,k1_xboole_0)) )),
% 0.21/0.48    inference(superposition,[],[f76,f144])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ( ! [X7] : (k1_xboole_0 = k5_xboole_0(X7,k5_xboole_0(k1_xboole_0,k4_xboole_0(X7,k1_xboole_0)))) )),
% 0.21/0.48    inference(superposition,[],[f74,f44])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X1),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)),k1_xboole_0))) )),
% 0.21/0.48    inference(superposition,[],[f103,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f23,f25,f25])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X3] : (k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(k1_xboole_0,X3),k1_xboole_0)) = X3) )),
% 0.21/0.48    inference(forward_demodulation,[],[f95,f44])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ( ! [X3] : (k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(k1_xboole_0,X3),k1_xboole_0)) = k5_xboole_0(X3,k1_xboole_0)) )),
% 0.21/0.48    inference(superposition,[],[f49,f67])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1))) )),
% 0.21/0.48    inference(superposition,[],[f29,f35])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.21/0.48    inference(superposition,[],[f32,f38])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X1,X2),k1_xboole_0)))) )),
% 0.21/0.48    inference(superposition,[],[f67,f29])).
% 0.21/0.48  fof(f338,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 0.21/0.48    inference(backward_demodulation,[],[f234,f330])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,k1_xboole_0),X3)) = X3) )),
% 0.21/0.48    inference(forward_demodulation,[],[f227,f225])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(X2,k1_xboole_0),X3))) = X3) )),
% 0.21/0.48    inference(backward_demodulation,[],[f193,f225])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(k4_xboole_0(X2,k1_xboole_0),X3)))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f183,f29])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(k1_xboole_0,k4_xboole_0(X2,k1_xboole_0)),X3))) )),
% 0.21/0.48    inference(superposition,[],[f29,f144])).
% 0.21/0.48  fof(f332,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f128,f330])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X0) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.48    inference(superposition,[],[f81,f37])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k1_tarski(sK0)))),
% 0.21/0.48    inference(definition_unfolding,[],[f18,f30,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f28,f27,f30])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f24,f27])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.48    inference(negated_conjecture,[],[f12])).
% 0.21/0.48  fof(f12,conjecture,(
% 0.21/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (3576)------------------------------
% 0.21/0.48  % (3576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3576)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (3576)Memory used [KB]: 6268
% 0.21/0.48  % (3576)Time elapsed: 0.016 s
% 0.21/0.48  % (3576)------------------------------
% 0.21/0.48  % (3576)------------------------------
% 0.21/0.48  % (3561)Success in time 0.122 s
%------------------------------------------------------------------------------
