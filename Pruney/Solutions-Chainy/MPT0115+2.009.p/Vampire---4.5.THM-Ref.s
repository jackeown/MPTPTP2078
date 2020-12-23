%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  93 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   17
%              Number of atoms          :   62 ( 124 expanded)
%              Number of equality atoms :   21 (  57 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f485,plain,(
    $false ),
    inference(resolution,[],[f471,f17])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f471,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f273,f18])).

fof(f18,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f273,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f210,f48])).

fof(f48,plain,(
    ! [X4,X2,X3] :
      ( k3_xboole_0(X2,k3_xboole_0(X3,X4)) = k3_xboole_0(X2,X4)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f26,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f210,plain,(
    ! [X4,X5,X3] : r1_tarski(k3_xboole_0(X3,k3_xboole_0(X4,X5)),X4) ),
    inference(resolution,[],[f170,f54])).

fof(f54,plain,(
    ! [X6,X7,X5] : r1_tarski(k3_xboole_0(X5,k3_xboole_0(X6,X7)),k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f21,f26])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f161,f24])).

fof(f161,plain,(
    ! [X4,X5,X3] : r1_tarski(k3_xboole_0(X3,k3_xboole_0(X4,X5)),X5) ),
    inference(superposition,[],[f141,f26])).

fof(f141,plain,(
    ! [X8,X7] : r1_tarski(k3_xboole_0(X7,X8),X8) ),
    inference(forward_demodulation,[],[f140,f20])).

fof(f20,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f140,plain,(
    ! [X8,X7] : r1_tarski(k5_xboole_0(k3_xboole_0(X7,X8),k1_xboole_0),X8) ),
    inference(forward_demodulation,[],[f139,f19])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f139,plain,(
    ! [X8,X7] : r1_tarski(k5_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k1_xboole_0)),X8) ),
    inference(forward_demodulation,[],[f138,f20])).

fof(f138,plain,(
    ! [X8,X7] : r1_tarski(k5_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k1_xboole_0)),k5_xboole_0(X8,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f137,f20])).

fof(f137,plain,(
    ! [X8,X7] : r1_tarski(k5_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k5_xboole_0(k1_xboole_0,k1_xboole_0))),k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f121,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f34,f21])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f24,f19])).

fof(f121,plain,(
    ! [X8,X7] : r1_tarski(k5_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k5_xboole_0(k1_xboole_0,k1_xboole_0))),k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X8)))) ),
    inference(superposition,[],[f96,f62])).

fof(f96,plain,(
    ! [X2,X0,X1] : r1_tarski(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X0,X1))))),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(forward_demodulation,[],[f95,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f30,f26])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f25,f22,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f95,plain,(
    ! [X2,X0,X1] : r1_tarski(k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X0,X1))))),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(forward_demodulation,[],[f31,f26])).

fof(f31,plain,(
    ! [X2,X0,X1] : r1_tarski(k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,X1)))),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(definition_unfolding,[],[f27,f29,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:43:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (18375)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (18368)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (18378)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (18370)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (18368)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f485,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(resolution,[],[f471,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,X2),X1) & r1_tarski(X0,X1)) => (~r1_tarski(k3_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,X2),X1) & r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.21/0.48    inference(negated_conjecture,[],[f11])).
% 0.21/0.48  fof(f11,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.21/0.48  fof(f471,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(resolution,[],[f273,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f273,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(superposition,[],[f210,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k3_xboole_0(X3,X4)) = k3_xboole_0(X2,X4) | ~r1_tarski(X2,X3)) )),
% 0.21/0.48    inference(superposition,[],[f26,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (r1_tarski(k3_xboole_0(X3,k3_xboole_0(X4,X5)),X4)) )),
% 0.21/0.48    inference(resolution,[],[f170,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X6,X7,X5] : (r1_tarski(k3_xboole_0(X5,k3_xboole_0(X6,X7)),k3_xboole_0(X5,X6))) )),
% 0.21/0.48    inference(superposition,[],[f21,f26])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X2)) )),
% 0.21/0.48    inference(superposition,[],[f161,f24])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (r1_tarski(k3_xboole_0(X3,k3_xboole_0(X4,X5)),X5)) )),
% 0.21/0.48    inference(superposition,[],[f141,f26])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ( ! [X8,X7] : (r1_tarski(k3_xboole_0(X7,X8),X8)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f140,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    ( ! [X8,X7] : (r1_tarski(k5_xboole_0(k3_xboole_0(X7,X8),k1_xboole_0),X8)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f139,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ( ! [X8,X7] : (r1_tarski(k5_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k1_xboole_0)),X8)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f138,f20])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ( ! [X8,X7] : (r1_tarski(k5_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k1_xboole_0)),k5_xboole_0(X8,k1_xboole_0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f137,f20])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ( ! [X8,X7] : (r1_tarski(k5_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k5_xboole_0(k1_xboole_0,k1_xboole_0))),k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,k1_xboole_0)))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f121,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(resolution,[],[f34,f21])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(superposition,[],[f24,f19])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ( ! [X8,X7] : (r1_tarski(k5_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k5_xboole_0(k1_xboole_0,k1_xboole_0))),k5_xboole_0(X8,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X8))))) )),
% 0.21/0.48    inference(superposition,[],[f96,f62])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X0,X1))))),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f95,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f30,f26])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f25,f22,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,k3_xboole_0(X2,k3_xboole_0(X0,X1))))),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f31,f26])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,X1)))),k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f27,f29,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f23,f22])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (18368)------------------------------
% 0.21/0.48  % (18368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18368)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (18368)Memory used [KB]: 6268
% 0.21/0.48  % (18368)Time elapsed: 0.058 s
% 0.21/0.48  % (18368)------------------------------
% 0.21/0.48  % (18368)------------------------------
% 0.21/0.48  % (18362)Success in time 0.116 s
%------------------------------------------------------------------------------
