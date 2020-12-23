%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:34 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 783 expanded)
%              Number of leaves         :   14 ( 266 expanded)
%              Depth                    :   18
%              Number of atoms          :   75 ( 788 expanded)
%              Number of equality atoms :   67 ( 780 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f440,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f439])).

fof(f439,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) ),
    inference(backward_demodulation,[],[f39,f438])).

fof(f438,plain,(
    ! [X6,X7] : k4_xboole_0(X7,X6) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6) ),
    inference(forward_demodulation,[],[f437,f294])).

fof(f294,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5 ),
    inference(superposition,[],[f284,f284])).

fof(f284,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f273,f23])).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f273,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f227,f170])).

fof(f170,plain,(
    ! [X2,X3] : k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3))) ),
    inference(backward_demodulation,[],[f92,f160])).

fof(f160,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f149,f159])).

fof(f159,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f156,f23])).

fof(f156,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f37,f149])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f149,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f137,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f137,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f42,f22])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f31,f31])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f92,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3))) = k4_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,X3)) ),
    inference(superposition,[],[f72,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f72,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f37,f40])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f227,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(forward_demodulation,[],[f224,f223])).

fof(f223,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f212,f23])).

fof(f212,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f164,f163])).

fof(f163,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f72,f160])).

fof(f164,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f93,f160])).

fof(f93,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X0),X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f34,f72])).

fof(f224,plain,(
    ! [X2,X1] : k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) = X2 ),
    inference(backward_demodulation,[],[f203,f223])).

fof(f203,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f34,f183])).

fof(f183,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1) ),
    inference(superposition,[],[f163,f54])).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f34,f23])).

fof(f437,plain,(
    ! [X6,X7] : k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6) = k5_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6) ),
    inference(forward_demodulation,[],[f420,f159])).

fof(f420,plain,(
    ! [X6,X7] : k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6) = k5_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),k4_xboole_0(X6,k1_xboole_0)) ),
    inference(superposition,[],[f141,f392])).

fof(f392,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X5,X4))) ),
    inference(forward_demodulation,[],[f382,f163])).

fof(f382,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X4) = k4_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X5,X4))) ),
    inference(superposition,[],[f37,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(resolution,[],[f43,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f26,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f141,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[],[f37,f42])).

fof(f39,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k1_tarski(sK0))) ),
    inference(definition_unfolding,[],[f21,f35,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f33,f29,f35])).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f21,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

% (22241)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% (22243)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f20,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19])).

fof(f19,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:51:44 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.46  % (22252)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.23/0.46  % (22242)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.47  % (22247)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.47  % (22247)Refutation not found, incomplete strategy% (22247)------------------------------
% 0.23/0.47  % (22247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.47  % (22247)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.47  
% 0.23/0.47  % (22247)Memory used [KB]: 10490
% 0.23/0.47  % (22247)Time elapsed: 0.048 s
% 0.23/0.47  % (22247)------------------------------
% 0.23/0.47  % (22247)------------------------------
% 0.23/0.47  % (22249)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.48  % (22239)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.48  % (22250)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.48  % (22246)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.48  % (22251)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.48  % (22240)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.48  % (22238)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.48  % (22250)Refutation found. Thanks to Tanya!
% 0.23/0.48  % SZS status Theorem for theBenchmark
% 0.23/0.48  % SZS output start Proof for theBenchmark
% 0.23/0.48  fof(f440,plain,(
% 0.23/0.48    $false),
% 0.23/0.48    inference(trivial_inequality_removal,[],[f439])).
% 0.23/0.48  fof(f439,plain,(
% 0.23/0.48    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),
% 0.23/0.48    inference(backward_demodulation,[],[f39,f438])).
% 0.23/0.48  fof(f438,plain,(
% 0.23/0.48    ( ! [X6,X7] : (k4_xboole_0(X7,X6) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6)) )),
% 0.23/0.48    inference(forward_demodulation,[],[f437,f294])).
% 0.23/0.48  fof(f294,plain,(
% 0.23/0.48    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5) )),
% 0.23/0.48    inference(superposition,[],[f284,f284])).
% 0.23/0.48  fof(f284,plain,(
% 0.23/0.48    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 0.23/0.48    inference(forward_demodulation,[],[f273,f23])).
% 0.23/0.48  fof(f23,plain,(
% 0.23/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f7])).
% 0.23/0.48  fof(f7,axiom,(
% 0.23/0.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.23/0.48  fof(f273,plain,(
% 0.23/0.48    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 0.23/0.48    inference(superposition,[],[f227,f170])).
% 0.23/0.48  fof(f170,plain,(
% 0.23/0.48    ( ! [X2,X3] : (k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3)))) )),
% 0.23/0.48    inference(backward_demodulation,[],[f92,f160])).
% 0.23/0.48  fof(f160,plain,(
% 0.23/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.23/0.48    inference(backward_demodulation,[],[f149,f159])).
% 0.23/0.48  fof(f159,plain,(
% 0.23/0.48    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.23/0.48    inference(forward_demodulation,[],[f156,f23])).
% 0.23/0.48  fof(f156,plain,(
% 0.23/0.48    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)) )),
% 0.23/0.48    inference(superposition,[],[f37,f149])).
% 0.23/0.48  fof(f37,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.23/0.48    inference(definition_unfolding,[],[f30,f31])).
% 0.23/0.48  fof(f31,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f5])).
% 0.23/0.48  fof(f5,axiom,(
% 0.23/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.48  fof(f30,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f3])).
% 0.23/0.48  fof(f3,axiom,(
% 0.23/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.23/0.48  fof(f149,plain,(
% 0.23/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.23/0.48    inference(forward_demodulation,[],[f137,f22])).
% 0.23/0.48  fof(f22,plain,(
% 0.23/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f6])).
% 0.23/0.48  fof(f6,axiom,(
% 0.23/0.48    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.23/0.48  fof(f137,plain,(
% 0.23/0.48    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.23/0.48    inference(superposition,[],[f42,f22])).
% 0.23/0.48  fof(f42,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.23/0.48    inference(definition_unfolding,[],[f27,f31,f31])).
% 0.23/0.48  fof(f27,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f1])).
% 0.23/0.48  fof(f1,axiom,(
% 0.23/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.48  fof(f92,plain,(
% 0.23/0.48    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3))) = k4_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,X3))) )),
% 0.23/0.48    inference(superposition,[],[f72,f34])).
% 0.23/0.48  fof(f34,plain,(
% 0.23/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f9])).
% 0.23/0.48  fof(f9,axiom,(
% 0.23/0.48    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.23/0.48  fof(f72,plain,(
% 0.23/0.48    ( ! [X1] : (k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)) )),
% 0.23/0.48    inference(superposition,[],[f37,f40])).
% 0.23/0.48  fof(f40,plain,(
% 0.23/0.48    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.23/0.48    inference(definition_unfolding,[],[f25,f31])).
% 0.23/0.48  fof(f25,plain,(
% 0.23/0.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.23/0.48    inference(cnf_transformation,[],[f16])).
% 0.23/0.48  fof(f16,plain,(
% 0.23/0.48    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.23/0.48    inference(rectify,[],[f2])).
% 0.23/0.48  fof(f2,axiom,(
% 0.23/0.48    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.23/0.48  fof(f227,plain,(
% 0.23/0.48    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2) )),
% 0.23/0.48    inference(forward_demodulation,[],[f224,f223])).
% 0.23/0.48  fof(f223,plain,(
% 0.23/0.48    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.23/0.48    inference(forward_demodulation,[],[f212,f23])).
% 0.23/0.48  fof(f212,plain,(
% 0.23/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.23/0.48    inference(superposition,[],[f164,f163])).
% 0.23/0.48  fof(f163,plain,(
% 0.23/0.48    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 0.23/0.48    inference(backward_demodulation,[],[f72,f160])).
% 0.23/0.48  fof(f164,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.23/0.48    inference(backward_demodulation,[],[f93,f160])).
% 0.23/0.48  fof(f93,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X0),X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.23/0.48    inference(superposition,[],[f34,f72])).
% 0.23/0.48  fof(f224,plain,(
% 0.23/0.48    ( ! [X2,X1] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) = X2) )),
% 0.23/0.48    inference(backward_demodulation,[],[f203,f223])).
% 0.23/0.48  fof(f203,plain,(
% 0.23/0.48    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2))) )),
% 0.23/0.48    inference(superposition,[],[f34,f183])).
% 0.23/0.48  fof(f183,plain,(
% 0.23/0.48    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)) )),
% 0.23/0.48    inference(superposition,[],[f163,f54])).
% 0.23/0.48  fof(f54,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 0.23/0.48    inference(superposition,[],[f34,f23])).
% 0.23/0.48  fof(f437,plain,(
% 0.23/0.48    ( ! [X6,X7] : (k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6) = k5_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6)) )),
% 0.23/0.48    inference(forward_demodulation,[],[f420,f159])).
% 0.23/0.48  fof(f420,plain,(
% 0.23/0.48    ( ! [X6,X7] : (k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),X6) = k5_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),k4_xboole_0(X6,k1_xboole_0))) )),
% 0.23/0.48    inference(superposition,[],[f141,f392])).
% 0.23/0.48  fof(f392,plain,(
% 0.23/0.48    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) )),
% 0.23/0.48    inference(forward_demodulation,[],[f382,f163])).
% 0.23/0.48  fof(f382,plain,(
% 0.23/0.48    ( ! [X4,X5] : (k5_xboole_0(X4,X4) = k4_xboole_0(X4,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) )),
% 0.23/0.48    inference(superposition,[],[f37,f51])).
% 0.23/0.48  fof(f51,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) )),
% 0.23/0.48    inference(resolution,[],[f43,f41])).
% 0.23/0.48  fof(f41,plain,(
% 0.23/0.48    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.23/0.48    inference(definition_unfolding,[],[f26,f29])).
% 0.23/0.48  fof(f29,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f10])).
% 0.23/0.48  fof(f10,axiom,(
% 0.23/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.23/0.48  fof(f26,plain,(
% 0.23/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f8])).
% 0.23/0.48  fof(f8,axiom,(
% 0.23/0.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.23/0.48  fof(f43,plain,(
% 0.23/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.23/0.48    inference(definition_unfolding,[],[f32,f31])).
% 0.23/0.48  fof(f32,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.23/0.48    inference(cnf_transformation,[],[f18])).
% 0.23/0.48  fof(f18,plain,(
% 0.23/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.23/0.48    inference(ennf_transformation,[],[f4])).
% 0.23/0.48  fof(f4,axiom,(
% 0.23/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.23/0.48  fof(f141,plain,(
% 0.23/0.48    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) )),
% 0.23/0.48    inference(superposition,[],[f37,f42])).
% 0.23/0.48  fof(f39,plain,(
% 0.23/0.48    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k1_tarski(sK0)))),
% 0.23/0.48    inference(definition_unfolding,[],[f21,f35,f36])).
% 0.23/0.48  fof(f36,plain,(
% 0.23/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.23/0.48    inference(definition_unfolding,[],[f33,f29,f35])).
% 0.23/0.48  fof(f33,plain,(
% 0.23/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f12])).
% 0.23/0.48  fof(f12,axiom,(
% 0.23/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.23/0.48  fof(f35,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))) )),
% 0.23/0.48    inference(definition_unfolding,[],[f28,f29])).
% 0.23/0.48  fof(f28,plain,(
% 0.23/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.23/0.48    inference(cnf_transformation,[],[f11])).
% 0.23/0.48  fof(f11,axiom,(
% 0.23/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.23/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.23/0.48  fof(f21,plain,(
% 0.23/0.48    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.23/0.48    inference(cnf_transformation,[],[f20])).
% 0.23/0.49  % (22241)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.49  % (22243)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.23/0.49  fof(f20,plain,(
% 0.23/0.49    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19])).
% 0.23/0.49  fof(f19,plain,(
% 0.23/0.49    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f17,plain,(
% 0.23/0.49    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 0.23/0.49    inference(ennf_transformation,[],[f15])).
% 0.23/0.49  fof(f15,negated_conjecture,(
% 0.23/0.49    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.23/0.49    inference(negated_conjecture,[],[f14])).
% 0.23/0.49  fof(f14,conjecture,(
% 0.23/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.23/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (22250)------------------------------
% 0.23/0.49  % (22250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (22250)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (22250)Memory used [KB]: 6268
% 0.23/0.49  % (22250)Time elapsed: 0.068 s
% 0.23/0.49  % (22250)------------------------------
% 0.23/0.49  % (22250)------------------------------
% 0.23/0.49  % (22253)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.23/0.49  % (22248)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.23/0.49  % (22237)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.23/0.49  % (22236)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.50  % (22245)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.23/0.50  % (22235)Success in time 0.127 s
%------------------------------------------------------------------------------
