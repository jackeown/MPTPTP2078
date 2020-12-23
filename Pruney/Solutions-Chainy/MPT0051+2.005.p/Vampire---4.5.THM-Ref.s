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
% DateTime   : Thu Dec  3 12:29:55 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   29 (  42 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :   14
%              Number of atoms          :   34 (  50 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f657,plain,(
    $false ),
    inference(subsumption_resolution,[],[f647,f11])).

fof(f11,plain,(
    ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
       => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f647,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f13,f547])).

fof(f547,plain,(
    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f87,f197])).

fof(f197,plain,(
    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f196,f14])).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f196,plain,(
    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f184,f14])).

fof(f184,plain,(
    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f104,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f104,plain,(
    ! [X0] : k2_xboole_0(sK2,X0) = k2_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f85,f14])).

fof(f85,plain,(
    ! [X17] : k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),X17)) = k2_xboole_0(sK2,X17) ),
    inference(superposition,[],[f18,f68])).

fof(f68,plain,(
    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f58,f12])).

fof(f12,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f58,plain,(
    k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f15,f35])).

fof(f35,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(resolution,[],[f16,f10])).

fof(f10,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f87,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f18,f14])).

fof(f13,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 12:47:45 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.43  % (21202)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.23/0.43  % (21203)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.23/0.43  % (21204)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.23/0.44  % (21205)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.23/0.45  % (21198)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.23/0.47  % (21198)Refutation found. Thanks to Tanya!
% 0.23/0.47  % SZS status Theorem for theBenchmark
% 0.23/0.47  % SZS output start Proof for theBenchmark
% 0.23/0.47  fof(f657,plain,(
% 0.23/0.47    $false),
% 0.23/0.47    inference(subsumption_resolution,[],[f647,f11])).
% 0.23/0.47  fof(f11,plain,(
% 0.23/0.47    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.23/0.47    inference(cnf_transformation,[],[f9])).
% 0.23/0.47  fof(f9,plain,(
% 0.23/0.47    ? [X0,X1,X2] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) & r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.23/0.47    inference(ennf_transformation,[],[f8])).
% 0.23/0.47  fof(f8,negated_conjecture,(
% 0.23/0.47    ~! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.23/0.47    inference(negated_conjecture,[],[f7])).
% 0.23/0.47  fof(f7,conjecture,(
% 0.23/0.47    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.23/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.23/0.47  fof(f647,plain,(
% 0.23/0.47    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.23/0.47    inference(superposition,[],[f13,f547])).
% 0.23/0.47  fof(f547,plain,(
% 0.23/0.47    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.23/0.47    inference(superposition,[],[f87,f197])).
% 0.23/0.47  fof(f197,plain,(
% 0.23/0.47    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 0.23/0.47    inference(forward_demodulation,[],[f196,f14])).
% 0.23/0.47  fof(f14,plain,(
% 0.23/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.23/0.47    inference(cnf_transformation,[],[f1])).
% 0.23/0.47  fof(f1,axiom,(
% 0.23/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.23/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.23/0.47  fof(f196,plain,(
% 0.23/0.47    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 0.23/0.47    inference(forward_demodulation,[],[f184,f14])).
% 0.23/0.47  fof(f184,plain,(
% 0.23/0.47    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK0))),
% 0.23/0.47    inference(superposition,[],[f104,f15])).
% 0.23/0.47  fof(f15,plain,(
% 0.23/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.23/0.47    inference(cnf_transformation,[],[f4])).
% 0.23/0.47  fof(f4,axiom,(
% 0.23/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.23/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.23/0.47  fof(f104,plain,(
% 0.23/0.47    ( ! [X0] : (k2_xboole_0(sK2,X0) = k2_xboole_0(sK2,k2_xboole_0(X0,k4_xboole_0(sK0,sK1)))) )),
% 0.23/0.47    inference(superposition,[],[f85,f14])).
% 0.23/0.47  fof(f85,plain,(
% 0.23/0.47    ( ! [X17] : (k2_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),X17)) = k2_xboole_0(sK2,X17)) )),
% 0.23/0.47    inference(superposition,[],[f18,f68])).
% 0.23/0.47  fof(f68,plain,(
% 0.23/0.47    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 0.23/0.47    inference(forward_demodulation,[],[f58,f12])).
% 0.23/0.47  fof(f12,plain,(
% 0.23/0.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.47    inference(cnf_transformation,[],[f2])).
% 0.23/0.47  fof(f2,axiom,(
% 0.23/0.47    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.23/0.47  fof(f58,plain,(
% 0.23/0.47    k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK2,k1_xboole_0)),
% 0.23/0.47    inference(superposition,[],[f15,f35])).
% 0.23/0.47  fof(f35,plain,(
% 0.23/0.47    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 0.23/0.47    inference(resolution,[],[f16,f10])).
% 0.23/0.47  fof(f10,plain,(
% 0.23/0.47    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.23/0.47    inference(cnf_transformation,[],[f9])).
% 0.23/0.47  fof(f16,plain,(
% 0.23/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.23/0.47    inference(cnf_transformation,[],[f3])).
% 0.23/0.47  fof(f3,axiom,(
% 0.23/0.47    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.23/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.23/0.47  fof(f18,plain,(
% 0.23/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.23/0.47    inference(cnf_transformation,[],[f5])).
% 0.23/0.47  fof(f5,axiom,(
% 0.23/0.47    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.23/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.23/0.47  fof(f87,plain,(
% 0.23/0.47    ( ! [X6,X7,X5] : (k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6))) )),
% 0.23/0.47    inference(superposition,[],[f18,f14])).
% 0.23/0.47  fof(f13,plain,(
% 0.23/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.23/0.47    inference(cnf_transformation,[],[f6])).
% 0.23/0.47  fof(f6,axiom,(
% 0.23/0.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.23/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.23/0.47  % SZS output end Proof for theBenchmark
% 0.23/0.47  % (21198)------------------------------
% 0.23/0.47  % (21198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.47  % (21198)Termination reason: Refutation
% 0.23/0.47  
% 0.23/0.47  % (21198)Memory used [KB]: 11129
% 0.23/0.47  % (21198)Time elapsed: 0.045 s
% 0.23/0.47  % (21198)------------------------------
% 0.23/0.47  % (21198)------------------------------
% 0.23/0.47  % (21197)Success in time 0.102 s
%------------------------------------------------------------------------------
