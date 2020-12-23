%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  48 expanded)
%              Number of leaves         :   11 (  16 expanded)
%              Depth                    :   15
%              Number of atoms          :   39 (  49 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(subsumption_resolution,[],[f17,f54])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(forward_demodulation,[],[f52,f20])).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k1_enumset1(X0,X0,X1)) ),
    inference(superposition,[],[f50,f18])).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_tarski(X0,X1),k1_enumset1(X0,X1,X2)) ),
    inference(forward_demodulation,[],[f48,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_tarski(X0,X1),k2_enumset1(X0,X0,X1,X2)) ),
    inference(superposition,[],[f46,f20])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : r1_tarski(k1_enumset1(X0,X1,X2),k2_enumset1(X0,X1,X2,X3)) ),
    inference(forward_demodulation,[],[f44,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : r1_tarski(k1_enumset1(X0,X1,X2),k3_enumset1(X0,X0,X1,X2,X3)) ),
    inference(superposition,[],[f42,f23])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : r1_tarski(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(forward_demodulation,[],[f40,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : r1_tarski(k2_enumset1(X0,X1,X2,X3),k4_enumset1(X0,X0,X1,X2,X3,X4)) ),
    inference(superposition,[],[f38,f24])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r1_tarski(k3_enumset1(X0,X1,X2,X3,X4),k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(forward_demodulation,[],[f36,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r1_tarski(k3_enumset1(X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) ),
    inference(superposition,[],[f34,f25])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : r1_tarski(k4_enumset1(X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ),
    inference(forward_demodulation,[],[f32,f27])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : r1_tarski(k4_enumset1(X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ),
    inference(superposition,[],[f30,f26])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : r1_tarski(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(superposition,[],[f19,f28])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f17,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] : ~ r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))
   => ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:14:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (7037)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.45  % (7037)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(subsumption_resolution,[],[f17,f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f52,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_enumset1(X0,X0,X1))) )),
% 0.21/0.45    inference(superposition,[],[f50,f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),k1_enumset1(X0,X1,X2))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f48,f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),k2_enumset1(X0,X0,X1,X2))) )),
% 0.21/0.45    inference(superposition,[],[f46,f20])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (r1_tarski(k1_enumset1(X0,X1,X2),k2_enumset1(X0,X1,X2,X3))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f44,f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (r1_tarski(k1_enumset1(X0,X1,X2),k3_enumset1(X0,X0,X1,X2,X3))) )),
% 0.21/0.45    inference(superposition,[],[f42,f23])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (r1_tarski(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X0,X1,X2,X3,X4))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f40,f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (r1_tarski(k2_enumset1(X0,X1,X2,X3),k4_enumset1(X0,X0,X1,X2,X3,X4))) )),
% 0.21/0.45    inference(superposition,[],[f38,f24])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tarski(k3_enumset1(X0,X1,X2,X3,X4),k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f36,f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tarski(k3_enumset1(X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) )),
% 0.21/0.45    inference(superposition,[],[f34,f25])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tarski(k4_enumset1(X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f32,f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tarski(k4_enumset1(X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) )),
% 0.21/0.45    inference(superposition,[],[f30,f26])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r1_tarski(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 0.21/0.45    inference(superposition,[],[f19,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ? [X0,X1] : ~r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) => ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ? [X0,X1] : ~r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.45    inference(negated_conjecture,[],[f12])).
% 0.21/0.45  fof(f12,conjecture,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (7037)------------------------------
% 0.21/0.45  % (7037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (7037)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (7037)Memory used [KB]: 6140
% 0.21/0.45  % (7037)Time elapsed: 0.006 s
% 0.21/0.45  % (7037)------------------------------
% 0.21/0.45  % (7037)------------------------------
% 0.21/0.45  % (7018)Success in time 0.091 s
%------------------------------------------------------------------------------
