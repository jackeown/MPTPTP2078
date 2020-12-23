%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  84 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :   15
%              Number of atoms          :   54 (  88 expanded)
%              Number of equality atoms :   46 (  80 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(forward_demodulation,[],[f200,f25])).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f200,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK1))) ),
    inference(forward_demodulation,[],[f199,f192])).

fof(f192,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f166,f42])).

fof(f42,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f25,f21])).

fof(f21,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f166,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f31,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f199,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK1))))) ),
    inference(backward_demodulation,[],[f87,f174])).

fof(f174,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f31,f25])).

fof(f87,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))))) ),
    inference(forward_demodulation,[],[f86,f25])).

fof(f86,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0))))) ),
    inference(backward_demodulation,[],[f41,f80])).

fof(f80,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(resolution,[],[f51,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) ),
    inference(superposition,[],[f37,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f23,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f41,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))))))) ),
    inference(forward_demodulation,[],[f40,f31])).

fof(f40,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))))))) ),
    inference(backward_demodulation,[],[f39,f31])).

fof(f39,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))))) ),
    inference(forward_demodulation,[],[f38,f24])).

fof(f38,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k1_tarski(sK0)))) ),
    inference(backward_demodulation,[],[f36,f24])).

% (30784)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% (30791)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% (30782)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% (30785)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% (30777)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f36,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f19,f33,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f30,f32,f33])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f19,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:26:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (30786)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (30781)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (30780)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (30783)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (30778)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (30779)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (30789)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (30776)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (30788)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (30789)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f202,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f201])).
% 0.20/0.48  fof(f201,plain,(
% 0.20/0.48    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))),
% 0.20/0.48    inference(forward_demodulation,[],[f200,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK1)))),
% 0.20/0.48    inference(forward_demodulation,[],[f199,f192])).
% 0.20/0.48  fof(f192,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.20/0.48    inference(forward_demodulation,[],[f166,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.20/0.48    inference(superposition,[],[f25,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.48  fof(f166,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.20/0.48    inference(superposition,[],[f31,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.48  fof(f199,plain,(
% 0.20/0.48    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK1)))))),
% 0.20/0.48    inference(backward_demodulation,[],[f87,f174])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 0.20/0.48    inference(superposition,[],[f31,f25])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))))),
% 0.20/0.48    inference(forward_demodulation,[],[f86,f25])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0)))))),
% 0.20/0.48    inference(backward_demodulation,[],[f41,f80])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0) )),
% 0.20/0.48    inference(resolution,[],[f51,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) )),
% 0.20/0.48    inference(superposition,[],[f37,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f23,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f28,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))))))))),
% 0.20/0.48    inference(forward_demodulation,[],[f40,f31])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))))))),
% 0.20/0.48    inference(backward_demodulation,[],[f39,f31])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))))))),
% 0.20/0.48    inference(forward_demodulation,[],[f38,f24])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k1_tarski(sK0))))),
% 0.20/0.48    inference(backward_demodulation,[],[f36,f24])).
% 0.20/0.48  % (30784)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (30791)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (30782)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (30785)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (30777)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0))))),
% 0.20/0.49    inference(definition_unfolding,[],[f19,f33,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0))))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f30,f32,f33])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0))))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f27,f32])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.49    inference(negated_conjecture,[],[f13])).
% 0.20/0.49  fof(f13,conjecture,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (30789)------------------------------
% 0.20/0.49  % (30789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (30789)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (30789)Memory used [KB]: 1663
% 0.20/0.49  % (30789)Time elapsed: 0.067 s
% 0.20/0.49  % (30789)------------------------------
% 0.20/0.49  % (30789)------------------------------
% 0.20/0.49  % (30775)Success in time 0.135 s
%------------------------------------------------------------------------------
