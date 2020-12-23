%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 276 expanded)
%              Number of leaves         :   10 (  95 expanded)
%              Depth                    :   17
%              Number of atoms          :   48 ( 277 expanded)
%              Number of equality atoms :   47 ( 276 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f423,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f422])).

fof(f422,plain,(
    k2_enumset1(sK0,sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(superposition,[],[f34,f307])).

fof(f307,plain,(
    ! [X14,X15,X13] : k2_enumset1(X13,X13,X14,X15) = k2_enumset1(X13,X13,X15,X14) ),
    inference(superposition,[],[f145,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X1,X1,X2)) ),
    inference(superposition,[],[f118,f32])).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(superposition,[],[f27,f26])).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f15,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X1,X2)) ),
    inference(definition_unfolding,[],[f18,f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f18,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(f15,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X1,X2,X3)) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f118,plain,(
    ! [X12,X10,X13,X11] : k2_enumset1(X10,X11,X12,X13) = k2_xboole_0(k2_enumset1(X11,X11,X11,X10),k2_enumset1(X12,X12,X12,X13)) ),
    inference(forward_demodulation,[],[f117,f27])).

fof(f117,plain,(
    ! [X12,X10,X13,X11] : k2_xboole_0(k1_tarski(X10),k2_enumset1(X10,X11,X12,X13)) = k2_xboole_0(k2_enumset1(X11,X11,X11,X10),k2_enumset1(X12,X12,X12,X13)) ),
    inference(forward_demodulation,[],[f116,f32])).

fof(f116,plain,(
    ! [X12,X10,X13,X11] : k2_xboole_0(k2_enumset1(X11,X11,X11,X10),k2_enumset1(X12,X12,X12,X13)) = k2_xboole_0(k2_enumset1(X10,X10,X10,X10),k2_enumset1(X10,X11,X12,X13)) ),
    inference(forward_demodulation,[],[f115,f27])).

fof(f115,plain,(
    ! [X12,X10,X13,X11] : k2_xboole_0(k2_enumset1(X10,X10,X10,X10),k2_xboole_0(k1_tarski(X10),k2_enumset1(X10,X11,X12,X13))) = k2_xboole_0(k2_enumset1(X11,X11,X11,X10),k2_enumset1(X12,X12,X12,X13)) ),
    inference(forward_demodulation,[],[f86,f27])).

fof(f86,plain,(
    ! [X12,X10,X13,X11] : k2_xboole_0(k2_enumset1(X10,X10,X10,X10),k2_xboole_0(k1_tarski(X10),k2_enumset1(X10,X11,X12,X13))) = k2_xboole_0(k2_xboole_0(k1_tarski(X11),k2_enumset1(X11,X11,X11,X10)),k2_enumset1(X12,X12,X12,X13)) ),
    inference(superposition,[],[f79,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X0,X1)) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f16,f24,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f17,f23])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)),k2_enumset1(X5,X5,X5,X6)) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_xboole_0(k1_tarski(X2),k2_enumset1(X3,X4,X5,X6))) ),
    inference(forward_demodulation,[],[f78,f27])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X0,X1)),k2_xboole_0(k1_tarski(X2),k2_enumset1(X3,X4,X5,X6))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)),k2_enumset1(X5,X5,X5,X6)) ),
    inference(forward_demodulation,[],[f30,f27])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X0,X1)),k2_xboole_0(k1_tarski(X2),k2_enumset1(X3,X4,X5,X6))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)),k2_xboole_0(k1_tarski(X5),k2_enumset1(X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f22,f25,f20,f24])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X0,X1)),k2_xboole_0(k1_tarski(X2),k2_enumset1(X3,X4,X5,X6))) ),
    inference(definition_unfolding,[],[f21,f24,f20])).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(f145,plain,(
    ! [X4,X2,X3] : k2_enumset1(X4,X4,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X3,X3,X3,X2)) ),
    inference(superposition,[],[f130,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(superposition,[],[f37,f27])).

fof(f37,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X1,X1,X1,X0)) ),
    inference(superposition,[],[f29,f27])).

fof(f34,plain,(
    k2_enumset1(sK0,sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK2,sK1) ),
    inference(forward_demodulation,[],[f31,f27])).

fof(f31,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK0,sK0,sK1,sK2)) != k2_enumset1(sK0,sK0,sK2,sK1) ),
    inference(backward_demodulation,[],[f28,f27])).

fof(f28,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK0,sK0,sK1,sK2)) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK0,sK0,sK2,sK1)) ),
    inference(definition_unfolding,[],[f14,f23,f23])).

fof(f14,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (22643)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (22656)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (22648)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (22653)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (22651)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (22652)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (22652)Refutation not found, incomplete strategy% (22652)------------------------------
% 0.20/0.47  % (22652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (22646)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (22654)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (22641)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (22644)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  % (22652)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (22652)Memory used [KB]: 10490
% 0.20/0.49  % (22652)Time elapsed: 0.061 s
% 0.20/0.49  % (22652)------------------------------
% 0.20/0.49  % (22652)------------------------------
% 0.20/0.49  % (22655)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (22658)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (22653)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f423,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f422])).
% 0.20/0.49  fof(f422,plain,(
% 0.20/0.49    k2_enumset1(sK0,sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.49    inference(superposition,[],[f34,f307])).
% 0.20/0.49  fof(f307,plain,(
% 0.20/0.49    ( ! [X14,X15,X13] : (k2_enumset1(X13,X13,X14,X15) = k2_enumset1(X13,X13,X15,X14)) )),
% 0.20/0.49    inference(superposition,[],[f145,f130])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X1,X1,X2))) )),
% 0.20/0.49    inference(superposition,[],[f118,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.49    inference(superposition,[],[f27,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X0,X0))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f15,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X1,X2))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f18,f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X1,X2,X3))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f19,f20])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ( ! [X12,X10,X13,X11] : (k2_enumset1(X10,X11,X12,X13) = k2_xboole_0(k2_enumset1(X11,X11,X11,X10),k2_enumset1(X12,X12,X12,X13))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f117,f27])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    ( ! [X12,X10,X13,X11] : (k2_xboole_0(k1_tarski(X10),k2_enumset1(X10,X11,X12,X13)) = k2_xboole_0(k2_enumset1(X11,X11,X11,X10),k2_enumset1(X12,X12,X12,X13))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f116,f32])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ( ! [X12,X10,X13,X11] : (k2_xboole_0(k2_enumset1(X11,X11,X11,X10),k2_enumset1(X12,X12,X12,X13)) = k2_xboole_0(k2_enumset1(X10,X10,X10,X10),k2_enumset1(X10,X11,X12,X13))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f115,f27])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ( ! [X12,X10,X13,X11] : (k2_xboole_0(k2_enumset1(X10,X10,X10,X10),k2_xboole_0(k1_tarski(X10),k2_enumset1(X10,X11,X12,X13))) = k2_xboole_0(k2_enumset1(X11,X11,X11,X10),k2_enumset1(X12,X12,X12,X13))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f86,f27])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ( ! [X12,X10,X13,X11] : (k2_xboole_0(k2_enumset1(X10,X10,X10,X10),k2_xboole_0(k1_tarski(X10),k2_enumset1(X10,X11,X12,X13))) = k2_xboole_0(k2_xboole_0(k1_tarski(X11),k2_enumset1(X11,X11,X11,X10)),k2_enumset1(X12,X12,X12,X13))) )),
% 0.20/0.49    inference(superposition,[],[f79,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X0,X1)) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X1,X1,X1,X0))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f16,f24,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f17,f23])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)),k2_enumset1(X5,X5,X5,X6)) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_xboole_0(k1_tarski(X2),k2_enumset1(X3,X4,X5,X6)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f78,f27])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X0,X1)),k2_xboole_0(k1_tarski(X2),k2_enumset1(X3,X4,X5,X6))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)),k2_enumset1(X5,X5,X5,X6))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f30,f27])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X0,X1)),k2_xboole_0(k1_tarski(X2),k2_enumset1(X3,X4,X5,X6))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)),k2_xboole_0(k1_tarski(X5),k2_enumset1(X5,X5,X5,X6)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f22,f25,f20,f24])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X0,X1)),k2_xboole_0(k1_tarski(X2),k2_enumset1(X3,X4,X5,X6)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f21,f24,f20])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    ( ! [X4,X2,X3] : (k2_enumset1(X4,X4,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X3,X3,X3,X2))) )),
% 0.20/0.49    inference(superposition,[],[f130,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.20/0.49    inference(superposition,[],[f37,f27])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X1,X1,X1,X0))) )),
% 0.20/0.49    inference(superposition,[],[f29,f27])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    k2_enumset1(sK0,sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK2,sK1)),
% 0.20/0.49    inference(forward_demodulation,[],[f31,f27])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK0,sK0,sK1,sK2)) != k2_enumset1(sK0,sK0,sK2,sK1)),
% 0.20/0.49    inference(backward_demodulation,[],[f28,f27])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK0,sK0,sK1,sK2)) != k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK0,sK0,sK2,sK1))),
% 0.20/0.49    inference(definition_unfolding,[],[f14,f23,f23])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1) => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1)),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1)),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 0.20/0.49    inference(negated_conjecture,[],[f9])).
% 0.20/0.49  fof(f9,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (22653)------------------------------
% 0.20/0.49  % (22653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (22653)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (22653)Memory used [KB]: 1791
% 0.20/0.49  % (22653)Time elapsed: 0.074 s
% 0.20/0.49  % (22653)------------------------------
% 0.20/0.49  % (22653)------------------------------
% 0.20/0.49  % (22649)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (22650)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (22640)Success in time 0.139 s
%------------------------------------------------------------------------------
