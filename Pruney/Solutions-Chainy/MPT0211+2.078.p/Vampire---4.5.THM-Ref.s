%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 396 expanded)
%              Number of leaves         :   15 ( 142 expanded)
%              Depth                    :   16
%              Number of atoms          :   58 ( 397 expanded)
%              Number of equality atoms :   57 ( 396 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f535,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f534])).

fof(f534,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(superposition,[],[f529,f97])).

fof(f97,plain,(
    ! [X19,X17,X18,X16] : k4_enumset1(X19,X19,X19,X17,X18,X16) = k4_enumset1(X19,X19,X19,X18,X17,X16) ),
    inference(superposition,[],[f51,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X1,X2,X0) ),
    inference(definition_unfolding,[],[f32,f40,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f33,f40,f40])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(f529,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2) ),
    inference(superposition,[],[f528,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f37,f39,f40,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f28,f40])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).

fof(f528,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(forward_demodulation,[],[f527,f204])).

fof(f204,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X1,X2,X3,X3) ),
    inference(superposition,[],[f52,f45])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),k3_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),k4_enumset1(X0,X0,X0,X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f35,f40,f39,f41,f43])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f42])).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f527,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(forward_demodulation,[],[f526,f204])).

fof(f526,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(forward_demodulation,[],[f446,f204])).

fof(f446,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK1)))) ),
    inference(backward_demodulation,[],[f138,f204])).

fof(f138,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f137,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X3,X2,X0) ),
    inference(definition_unfolding,[],[f31,f40,f40])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).

fof(f137,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK0,sK2,sK2),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK0,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f136,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f30,f40,f40])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(f136,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f135,f49])).

fof(f135,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK0,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f46,f48])).

fof(f46,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0)))) ),
    inference(definition_unfolding,[],[f22,f41,f39,f42,f42])).

fof(f22,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 16:16:37 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.49  % (11534)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (11539)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (11532)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (11540)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (11535)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (11547)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (11533)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (11542)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (11536)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (11537)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (11545)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % (11531)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.52  % (11546)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (11541)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.52  % (11541)Refutation not found, incomplete strategy% (11541)------------------------------
% 0.22/0.52  % (11541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (11541)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (11541)Memory used [KB]: 10618
% 0.22/0.52  % (11541)Time elapsed: 0.095 s
% 0.22/0.52  % (11541)------------------------------
% 0.22/0.52  % (11541)------------------------------
% 0.22/0.53  % (11530)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.53  % (11538)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.54  % (11534)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f535,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f534])).
% 0.22/0.54  fof(f534,plain,(
% 0.22/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.22/0.54    inference(superposition,[],[f529,f97])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X19,X17,X18,X16] : (k4_enumset1(X19,X19,X19,X17,X18,X16) = k4_enumset1(X19,X19,X19,X18,X17,X16)) )),
% 0.22/0.54    inference(superposition,[],[f51,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X1,X2,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f32,f40,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f34,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_enumset1)).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X3,X3,X3,X2,X1,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f33,f40,f40])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 0.22/0.54  fof(f529,plain,(
% 0.22/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK1,sK0,sK2)),
% 0.22/0.54    inference(superposition,[],[f528,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3))))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f37,f39,f40,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f24,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f28,f40])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f26,f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).
% 0.22/0.54  fof(f528,plain,(
% 0.22/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))),
% 0.22/0.54    inference(forward_demodulation,[],[f527,f204])).
% 0.22/0.54  fof(f204,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X1,X2,X3,X3)) )),
% 0.22/0.54    inference(superposition,[],[f52,f45])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,X2),k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),k3_xboole_0(k4_enumset1(X3,X3,X3,X3,X3,X3),k4_enumset1(X0,X0,X0,X0,X1,X2))))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f35,f40,f39,f41,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f23,f42])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.22/0.54  fof(f527,plain,(
% 0.22/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))),
% 0.22/0.54    inference(forward_demodulation,[],[f526,f204])).
% 0.22/0.54  fof(f526,plain,(
% 0.22/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))),
% 0.22/0.54    inference(forward_demodulation,[],[f446,f204])).
% 0.22/0.54  fof(f446,plain,(
% 0.22/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK1))))),
% 0.22/0.54    inference(backward_demodulation,[],[f138,f204])).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK2,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))),
% 0.22/0.54    inference(forward_demodulation,[],[f137,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X1,X1,X1,X3,X2,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f31,f40,f40])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_enumset1)).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK0,sK2,sK2),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK0,sK2,sK2),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))),
% 0.22/0.54    inference(forward_demodulation,[],[f136,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X3,X2,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f30,f40,f40])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK0,sK0,sK0,sK1,sK1,sK1))))),
% 0.22/0.54    inference(forward_demodulation,[],[f135,f49])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK0,sK1,sK1),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK0,sK1,sK1))))),
% 0.22/0.54    inference(forward_demodulation,[],[f46,f48])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k4_enumset1(sK2,sK2,sK2,sK2,sK2,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK0))))),
% 0.22/0.54    inference(definition_unfolding,[],[f22,f41,f39,f42,f42])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.22/0.54    inference(negated_conjecture,[],[f17])).
% 0.22/0.54  fof(f17,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (11534)------------------------------
% 0.22/0.54  % (11534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11534)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (11534)Memory used [KB]: 6524
% 0.22/0.54  % (11534)Time elapsed: 0.104 s
% 0.22/0.54  % (11534)------------------------------
% 0.22/0.54  % (11534)------------------------------
% 0.22/0.54  % (11529)Success in time 0.172 s
%------------------------------------------------------------------------------
