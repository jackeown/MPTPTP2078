%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 226 expanded)
%              Number of leaves         :   13 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          :   97 ( 338 expanded)
%              Number of equality atoms :   41 ( 163 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1273,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1272,f1062])).

fof(f1062,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f1045,f21])).

fof(f21,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f1045,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f527,f81])).

fof(f81,plain,(
    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f30,f34])).

fof(f34,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f20,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f20,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f527,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) ),
    inference(superposition,[],[f476,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f33,f29,f29])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f476,plain,(
    ! [X2,X1] : r1_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X1) ),
    inference(superposition,[],[f442,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f442,plain,(
    ! [X10,X11] : r1_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),X10) ),
    inference(forward_demodulation,[],[f441,f59])).

fof(f59,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f35,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f23,f29])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f441,plain,(
    ! [X10,X11] : r1_xboole_0(k5_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),k1_xboole_0),X10) ),
    inference(forward_demodulation,[],[f440,f390])).

fof(f390,plain,(
    ! [X4,X5] : k1_xboole_0 = k3_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X4,X5))) ),
    inference(forward_demodulation,[],[f389,f113])).

% (16570)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f113,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f76,f27])).

fof(f76,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(k3_xboole_0(X3,X4),X4) ),
    inference(resolution,[],[f30,f46])).

fof(f46,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f389,plain,(
    ! [X4,X5] : k1_xboole_0 = k3_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,k3_xboole_0(X4,X5)))) ),
    inference(forward_demodulation,[],[f362,f145])).

fof(f145,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f136,f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f136,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(resolution,[],[f38,f42])).

fof(f42,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(superposition,[],[f26,f24])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f32,f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f362,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,k3_xboole_0(X4,X5)))) = k5_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f40,f24])).

fof(f440,plain,(
    ! [X10,X11] : r1_xboole_0(k5_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),k3_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X10,X11)))),X10) ),
    inference(forward_demodulation,[],[f439,f27])).

fof(f439,plain,(
    ! [X10,X11] : r1_xboole_0(k5_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),k3_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),X10)),X10) ),
    inference(forward_demodulation,[],[f413,f59])).

fof(f413,plain,(
    ! [X10,X11] : r1_xboole_0(k5_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),k3_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),X10)),k5_xboole_0(X10,k1_xboole_0)) ),
    inference(superposition,[],[f37,f390])).

fof(f37,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f28,f29,f29])).

fof(f28,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

fof(f1272,plain,(
    r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1240,f153])).

fof(f153,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f144,f81])).

fof(f144,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f38,f34])).

fof(f1240,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f39,f1178])).

fof(f1178,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f1176,f95])).

fof(f95,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f75,f27])).

fof(f75,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k3_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(resolution,[],[f30,f26])).

% (16568)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f1176,plain,(
    sK0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f1131,f30])).

fof(f1131,plain,(
    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f373,f81])).

fof(f373,plain,(
    ! [X17,X15,X16] : r1_tarski(k3_xboole_0(X15,k5_xboole_0(X16,k3_xboole_0(X16,X17))),k3_xboole_0(X15,X16)) ),
    inference(superposition,[],[f36,f40])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f25,f29])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f29])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:14:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (16576)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.45  % (16569)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (16573)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.46  % (16578)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (16564)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (16576)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f1273,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f1272,f1062])).
% 0.20/0.47  fof(f1062,plain,(
% 0.20/0.47    ~r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(resolution,[],[f1045,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.47    inference(negated_conjecture,[],[f12])).
% 0.20/0.47  fof(f12,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.20/0.47  fof(f1045,plain,(
% 0.20/0.47    r1_xboole_0(sK0,sK2)),
% 0.20/0.47    inference(superposition,[],[f527,f81])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.20/0.47    inference(resolution,[],[f30,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 0.20/0.47    inference(definition_unfolding,[],[f20,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.47  fof(f527,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2)) )),
% 0.20/0.47    inference(superposition,[],[f476,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f33,f29,f29])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.47  fof(f476,plain,(
% 0.20/0.47    ( ! [X2,X1] : (r1_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X1)) )),
% 0.20/0.47    inference(superposition,[],[f442,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.47  fof(f442,plain,(
% 0.20/0.47    ( ! [X10,X11] : (r1_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),X10)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f441,f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.47    inference(forward_demodulation,[],[f35,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.20/0.47    inference(definition_unfolding,[],[f23,f29])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.47  fof(f441,plain,(
% 0.20/0.47    ( ! [X10,X11] : (r1_xboole_0(k5_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),k1_xboole_0),X10)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f440,f390])).
% 0.20/0.47  fof(f390,plain,(
% 0.20/0.47    ( ! [X4,X5] : (k1_xboole_0 = k3_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X4,X5)))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f389,f113])).
% 0.20/0.47  % (16570)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k3_xboole_0(X5,k3_xboole_0(X4,X5))) )),
% 0.20/0.47    inference(superposition,[],[f76,f27])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(k3_xboole_0(X3,X4),X4)) )),
% 0.20/0.47    inference(resolution,[],[f30,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X3,X2),X2)) )),
% 0.20/0.47    inference(superposition,[],[f26,f27])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.47  fof(f389,plain,(
% 0.20/0.47    ( ! [X4,X5] : (k1_xboole_0 = k3_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,k3_xboole_0(X4,X5))))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f362,f145])).
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f136,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.47    inference(rectify,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 0.20/0.47    inference(resolution,[],[f38,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.47    inference(superposition,[],[f26,f24])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f32,f29])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.47    inference(nnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.47  fof(f362,plain,(
% 0.20/0.47    ( ! [X4,X5] : (k3_xboole_0(X4,k5_xboole_0(X5,k3_xboole_0(X5,k3_xboole_0(X4,X5)))) = k5_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(X4,X5))) )),
% 0.20/0.47    inference(superposition,[],[f40,f24])).
% 0.20/0.47  fof(f440,plain,(
% 0.20/0.47    ( ! [X10,X11] : (r1_xboole_0(k5_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),k3_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X10,X11)))),X10)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f439,f27])).
% 0.20/0.47  fof(f439,plain,(
% 0.20/0.47    ( ! [X10,X11] : (r1_xboole_0(k5_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),k3_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),X10)),X10)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f413,f59])).
% 0.20/0.47  fof(f413,plain,(
% 0.20/0.47    ( ! [X10,X11] : (r1_xboole_0(k5_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),k3_xboole_0(k5_xboole_0(X11,k3_xboole_0(X10,X11)),X10)),k5_xboole_0(X10,k1_xboole_0))) )),
% 0.20/0.47    inference(superposition,[],[f37,f390])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f28,f29,f29])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).
% 0.20/0.47  fof(f1272,plain,(
% 0.20/0.47    r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f1240,f153])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 0.20/0.47    inference(forward_demodulation,[],[f144,f81])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))),
% 0.20/0.47    inference(resolution,[],[f38,f34])).
% 0.20/0.47  fof(f1240,plain,(
% 0.20/0.47    k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,sK1)),
% 0.20/0.47    inference(superposition,[],[f39,f1178])).
% 0.20/0.47  fof(f1178,plain,(
% 0.20/0.47    sK0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.47    inference(superposition,[],[f1176,f95])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 0.20/0.47    inference(superposition,[],[f75,f27])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k3_xboole_0(k3_xboole_0(X1,X2),X1)) )),
% 0.20/0.47    inference(resolution,[],[f30,f26])).
% 0.20/0.47  % (16568)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  fof(f1176,plain,(
% 0.20/0.47    sK0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.47    inference(resolution,[],[f1131,f30])).
% 0.20/0.47  fof(f1131,plain,(
% 0.20/0.47    r1_tarski(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.47    inference(superposition,[],[f373,f81])).
% 0.20/0.47  fof(f373,plain,(
% 0.20/0.47    ( ! [X17,X15,X16] : (r1_tarski(k3_xboole_0(X15,k5_xboole_0(X16,k3_xboole_0(X16,X17))),k3_xboole_0(X15,X16))) )),
% 0.20/0.47    inference(superposition,[],[f36,f40])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f25,f29])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f31,f29])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (16576)------------------------------
% 0.20/0.47  % (16576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (16576)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (16576)Memory used [KB]: 2046
% 0.20/0.47  % (16576)Time elapsed: 0.023 s
% 0.20/0.47  % (16576)------------------------------
% 0.20/0.47  % (16576)------------------------------
% 0.20/0.47  % (16571)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (16560)Success in time 0.109 s
%------------------------------------------------------------------------------
