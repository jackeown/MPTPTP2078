%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 (  49 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :   14
%              Number of atoms          :   47 (  55 expanded)
%              Number of equality atoms :   35 (  43 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(subsumption_resolution,[],[f33,f85])).

fof(f85,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f83,f22])).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2)) ),
    inference(forward_demodulation,[],[f80,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X1,X2)) ),
    inference(superposition,[],[f78,f20])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),k2_enumset1(X0,X1,X2,X3)) ),
    inference(forward_demodulation,[],[f75,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),k3_enumset1(X0,X0,X1,X2,X3)) ),
    inference(superposition,[],[f73,f22])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k1_xboole_0 = k4_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(forward_demodulation,[],[f70,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k1_xboole_0 = k4_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X0,X0,X1,X2,X3,X4)) ),
    inference(superposition,[],[f68,f27])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(forward_demodulation,[],[f65,f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X1,X2,X3),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) ),
    inference(superposition,[],[f63,f28])).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k1_xboole_0 = k4_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ),
    inference(forward_demodulation,[],[f60,f31])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k1_xboole_0 = k4_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ),
    inference(superposition,[],[f58,f29])).

fof(f58,plain,(
    ! [X47,X45,X43,X41,X46,X44,X42,X40] : k1_xboole_0 = k4_xboole_0(k4_enumset1(X40,X41,X42,X43,X44,X45),k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47)) ),
    inference(superposition,[],[f21,f32])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f33,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(resolution,[],[f25,f19])).

fof(f19,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] : ~ r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))
   => ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (1539)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.43  % (1539)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(subsumption_resolution,[],[f33,f85])).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.20/0.43    inference(superposition,[],[f83,f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f80,f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_enumset1(X0,X0,X1,X2))) )),
% 0.20/0.43    inference(superposition,[],[f78,f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),k2_enumset1(X0,X1,X2,X3))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f75,f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),k3_enumset1(X0,X0,X1,X2,X3))) )),
% 0.20/0.43    inference(superposition,[],[f73,f22])).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = k4_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X0,X1,X2,X3,X4))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f70,f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = k4_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X0,X0,X1,X2,X3,X4))) )),
% 0.20/0.43    inference(superposition,[],[f68,f27])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f65,f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X1,X2,X3),k5_enumset1(X0,X0,X1,X2,X3,X4,X5))) )),
% 0.20/0.43    inference(superposition,[],[f63,f28])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k1_xboole_0 = k4_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f60,f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k1_xboole_0 = k4_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) )),
% 0.20/0.43    inference(superposition,[],[f58,f29])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    ( ! [X47,X45,X43,X41,X46,X44,X42,X40] : (k1_xboole_0 = k4_xboole_0(k4_enumset1(X40,X41,X42,X43,X44,X45),k6_enumset1(X40,X41,X42,X43,X44,X45,X46,X47))) )),
% 0.20/0.43    inference(superposition,[],[f21,f32])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.20/0.43    inference(resolution,[],[f25,f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ? [X0,X1] : ~r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) => ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ? [X0,X1] : ~r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.43    inference(negated_conjecture,[],[f13])).
% 0.20/0.43  fof(f13,conjecture,(
% 0.20/0.43    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.43    inference(nnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (1539)------------------------------
% 0.20/0.43  % (1539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (1539)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (1539)Memory used [KB]: 6140
% 0.20/0.43  % (1539)Time elapsed: 0.030 s
% 0.20/0.43  % (1539)------------------------------
% 0.20/0.43  % (1539)------------------------------
% 0.20/0.43  % (1522)Success in time 0.075 s
%------------------------------------------------------------------------------
