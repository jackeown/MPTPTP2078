%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 137 expanded)
%              Number of leaves         :   12 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :   95 ( 233 expanded)
%              Number of equality atoms :   40 (  94 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f370,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f369])).

fof(f369,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f368,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f71,f26])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f39,f69])).

fof(f69,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f68,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f68,plain,(
    ! [X1] : r1_xboole_0(k1_xboole_0,X1) ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f63,f26])).

fof(f63,plain,(
    ! [X1] :
      ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f38,f56])).

fof(f56,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f52,f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f32,f28])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f34,f31])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f368,plain,(
    k1_xboole_0 != k4_xboole_0(sK2,sK2) ),
    inference(forward_demodulation,[],[f365,f363])).

fof(f363,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f362,f57])).

fof(f57,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3 ),
    inference(superposition,[],[f52,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f362,plain,(
    k4_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f355,f32])).

fof(f355,plain,(
    r1_tarski(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f296,f257])).

fof(f257,plain,(
    sK2 = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f256,f57])).

fof(f256,plain,(
    k4_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f248,f32])).

fof(f248,plain,(
    r1_tarski(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(forward_demodulation,[],[f233,f26])).

fof(f233,plain,(
    r1_tarski(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f165,f74])).

fof(f74,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f39,f41])).

fof(f41,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f33,f23])).

fof(f23,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f165,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2) ),
    inference(superposition,[],[f28,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f29,f31,f31])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f296,plain,(
    ! [X18] : r1_tarski(k4_xboole_0(X18,sK1),k4_xboole_0(X18,sK0)) ),
    inference(superposition,[],[f109,f51])).

fof(f51,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f32,f22])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f109,plain,(
    ! [X10,X8,X9] : r1_tarski(k4_xboole_0(X8,k2_xboole_0(X9,X10)),k4_xboole_0(X8,X9)) ),
    inference(superposition,[],[f28,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f365,plain,(
    k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f164,f24])).

fof(f24,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f164,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X1,k4_xboole_0(X1,X0)) ) ),
    inference(superposition,[],[f38,f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (12462)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.45  % (12450)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (12465)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (12458)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (12450)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f370,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f369])).
% 0.21/0.47  fof(f369,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0),
% 0.21/0.47    inference(superposition,[],[f368,f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f71,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.47    inference(resolution,[],[f39,f69])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(resolution,[],[f68,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X1] : (r1_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f67])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f63,f26])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ( ! [X1] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | r1_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.47    inference(superposition,[],[f38,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 0.21/0.47    inference(superposition,[],[f52,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 0.21/0.47    inference(resolution,[],[f32,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f35,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(nnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f34,f31])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f368,plain,(
% 0.21/0.47    k1_xboole_0 != k4_xboole_0(sK2,sK2)),
% 0.21/0.47    inference(forward_demodulation,[],[f365,f363])).
% 0.21/0.47  fof(f363,plain,(
% 0.21/0.47    sK2 = k4_xboole_0(sK2,sK0)),
% 0.21/0.47    inference(forward_demodulation,[],[f362,f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3) )),
% 0.21/0.47    inference(superposition,[],[f52,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.47  fof(f362,plain,(
% 0.21/0.47    k4_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 0.21/0.47    inference(resolution,[],[f355,f32])).
% 0.21/0.47  fof(f355,plain,(
% 0.21/0.47    r1_tarski(sK2,k4_xboole_0(sK2,sK0))),
% 0.21/0.47    inference(superposition,[],[f296,f257])).
% 0.21/0.47  fof(f257,plain,(
% 0.21/0.47    sK2 = k4_xboole_0(sK2,sK1)),
% 0.21/0.47    inference(forward_demodulation,[],[f256,f57])).
% 0.21/0.47  fof(f256,plain,(
% 0.21/0.47    k4_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 0.21/0.47    inference(resolution,[],[f248,f32])).
% 0.21/0.47  fof(f248,plain,(
% 0.21/0.47    r1_tarski(sK2,k4_xboole_0(sK2,sK1))),
% 0.21/0.47    inference(forward_demodulation,[],[f233,f26])).
% 0.21/0.47  fof(f233,plain,(
% 0.21/0.47    r1_tarski(k4_xboole_0(sK2,k1_xboole_0),k4_xboole_0(sK2,sK1))),
% 0.21/0.47    inference(superposition,[],[f165,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 0.21/0.47    inference(resolution,[],[f39,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    r1_xboole_0(sK2,sK1)),
% 0.21/0.47    inference(resolution,[],[f33,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    r1_xboole_0(sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.47    inference(negated_conjecture,[],[f12])).
% 0.21/0.47  fof(f12,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.47  fof(f165,plain,(
% 0.21/0.47    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,X2)),X2)) )),
% 0.21/0.47    inference(superposition,[],[f28,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f29,f31,f31])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.47  fof(f296,plain,(
% 0.21/0.47    ( ! [X18] : (r1_tarski(k4_xboole_0(X18,sK1),k4_xboole_0(X18,sK0))) )),
% 0.21/0.47    inference(superposition,[],[f109,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    sK1 = k2_xboole_0(sK0,sK1)),
% 0.21/0.47    inference(resolution,[],[f32,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    r1_tarski(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ( ! [X10,X8,X9] : (r1_tarski(k4_xboole_0(X8,k2_xboole_0(X9,X10)),k4_xboole_0(X8,X9))) )),
% 0.21/0.47    inference(superposition,[],[f28,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.47  fof(f365,plain,(
% 0.21/0.47    k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 0.21/0.47    inference(resolution,[],[f164,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ~r1_xboole_0(sK0,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(superposition,[],[f38,f37])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (12450)------------------------------
% 0.21/0.47  % (12450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (12450)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (12450)Memory used [KB]: 1791
% 0.21/0.47  % (12450)Time elapsed: 0.058 s
% 0.21/0.47  % (12450)------------------------------
% 0.21/0.47  % (12450)------------------------------
% 0.21/0.47  % (12444)Success in time 0.116 s
%------------------------------------------------------------------------------
