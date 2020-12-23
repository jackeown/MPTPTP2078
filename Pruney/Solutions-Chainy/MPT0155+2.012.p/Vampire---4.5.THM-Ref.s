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
% DateTime   : Thu Dec  3 12:33:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  94 expanded)
%              Number of leaves         :    8 (  31 expanded)
%              Depth                    :   15
%              Number of atoms          :   37 (  95 expanded)
%              Number of equality atoms :   36 (  94 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f190])).

fof(f190,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(superposition,[],[f23,f186])).

fof(f186,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(forward_demodulation,[],[f184,f142])).

fof(f142,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k2_xboole_0(k1_tarski(X3),k2_tarski(X4,X5)) ),
    inference(forward_demodulation,[],[f141,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f141,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k1_tarski(X3),k2_tarski(X4,X5)) = k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5)) ),
    inference(forward_demodulation,[],[f132,f24])).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f132,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k1_tarski(X3),k2_tarski(X4,X5)) = k2_xboole_0(k2_tarski(X3,X4),k2_tarski(X5,X5)) ),
    inference(superposition,[],[f64,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) = k3_enumset1(X2,X0,X1,X1,X1) ),
    inference(superposition,[],[f32,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_enumset1(X1,X0,X0,X0) = k2_tarski(X1,X0) ),
    inference(forward_demodulation,[],[f60,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(forward_demodulation,[],[f45,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(superposition,[],[f29,f24])).

fof(f60,plain,(
    ! [X0,X1] : k2_enumset1(X1,X0,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(superposition,[],[f59,f24])).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f31,f26])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X2,X3,X0,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f33,f26])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f184,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(superposition,[],[f152,f24])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) = k2_enumset1(X2,X3,X0,X1) ),
    inference(backward_demodulation,[],[f64,f151])).

fof(f151,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X3,X0,X1,X1,X2) = k2_enumset1(X3,X0,X1,X2) ),
    inference(forward_demodulation,[],[f147,f31])).

fof(f147,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X3,X0,X1,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) ),
    inference(backward_demodulation,[],[f61,f142])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X3,X0,X1,X1,X2) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) ),
    inference(superposition,[],[f32,f59])).

fof(f23,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:16:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (17677)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (17676)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (17679)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (17681)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (17682)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (17679)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f194,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f190])).
% 0.22/0.48  fof(f190,plain,(
% 0.22/0.48    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)),
% 0.22/0.48    inference(superposition,[],[f23,f186])).
% 0.22/0.48  fof(f186,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f184,f142])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k2_xboole_0(k1_tarski(X3),k2_tarski(X4,X5))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f141,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (k2_xboole_0(k1_tarski(X3),k2_tarski(X4,X5)) = k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f132,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,axiom,(
% 0.22/0.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (k2_xboole_0(k1_tarski(X3),k2_tarski(X4,X5)) = k2_xboole_0(k2_tarski(X3,X4),k2_tarski(X5,X5))) )),
% 0.22/0.48    inference(superposition,[],[f64,f67])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) = k3_enumset1(X2,X0,X1,X1,X1)) )),
% 0.22/0.48    inference(superposition,[],[f32,f62])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_enumset1(X1,X0,X0,X0) = k2_tarski(X1,X0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f60,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f45,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.48    inference(superposition,[],[f29,f24])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_enumset1(X1,X0,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 0.22/0.48    inference(superposition,[],[f59,f24])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X2,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) )),
% 0.22/0.48    inference(superposition,[],[f31,f26])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X2,X3,X0,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) )),
% 0.22/0.48    inference(superposition,[],[f33,f26])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 0.22/0.48  fof(f184,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.48    inference(superposition,[],[f152,f24])).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) = k2_enumset1(X2,X3,X0,X1)) )),
% 0.22/0.48    inference(backward_demodulation,[],[f64,f151])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X3,X0,X1,X1,X2) = k2_enumset1(X3,X0,X1,X2)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f147,f31])).
% 0.22/0.48  fof(f147,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X3,X0,X1,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) )),
% 0.22/0.48    inference(backward_demodulation,[],[f61,f142])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X3,X0,X1,X1,X2) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)))) )),
% 0.22/0.48    inference(superposition,[],[f32,f59])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.48    inference(ennf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.48    inference(negated_conjecture,[],[f18])).
% 0.22/0.48  fof(f18,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (17679)------------------------------
% 0.22/0.48  % (17679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (17679)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (17679)Memory used [KB]: 1791
% 0.22/0.48  % (17679)Time elapsed: 0.066 s
% 0.22/0.48  % (17679)------------------------------
% 0.22/0.48  % (17679)------------------------------
% 0.22/0.48  % (17675)Success in time 0.116 s
%------------------------------------------------------------------------------
