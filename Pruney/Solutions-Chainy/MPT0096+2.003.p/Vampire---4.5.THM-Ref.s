%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  43 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  58 expanded)
%              Number of equality atoms :   25 (  33 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1150,plain,(
    $false ),
    inference(resolution,[],[f1077,f27])).

fof(f27,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f17,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f17,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
   => ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).

fof(f1077,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(subsumption_resolution,[],[f1031,f77])).

fof(f77,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f26,f34])).

fof(f34,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(resolution,[],[f25,f31])).

fof(f31,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f20,f28])).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1031,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0)))
      | r1_xboole_0(k4_xboole_0(X1,X0),X0) ) ),
    inference(superposition,[],[f92,f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f92,plain,(
    ! [X6,X4,X5] :
      ( k1_xboole_0 != k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,k2_xboole_0(X5,X6))))
      | r1_xboole_0(k4_xboole_0(X4,X5),X6) ) ),
    inference(forward_demodulation,[],[f81,f26])).

fof(f81,plain,(
    ! [X6,X4,X5] :
      ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,k2_xboole_0(X5,X6)))
      | r1_xboole_0(k4_xboole_0(X4,X5),X6) ) ),
    inference(superposition,[],[f29,f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (4195)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.43  % (4195)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f1150,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(resolution,[],[f1077,f27])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 0.22/0.43    inference(definition_unfolding,[],[f17,f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,axiom,(
% 0.22/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) => ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 0.22/0.43    inference(negated_conjecture,[],[f8])).
% 0.22/0.43  fof(f8,conjecture,(
% 0.22/0.43    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).
% 0.22/0.43  fof(f1077,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f1031,f77])).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 0.22/0.43    inference(superposition,[],[f26,f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 0.22/0.43    inference(resolution,[],[f25,f31])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.43    inference(superposition,[],[f20,f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.22/0.43    inference(definition_unfolding,[],[f19,f21])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.43    inference(rectify,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.22/0.43    inference(nnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.43  fof(f1031,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) | r1_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 0.22/0.43    inference(superposition,[],[f92,f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.43    inference(rectify,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.43  fof(f92,plain,(
% 0.22/0.43    ( ! [X6,X4,X5] : (k1_xboole_0 != k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,k2_xboole_0(X5,X6)))) | r1_xboole_0(k4_xboole_0(X4,X5),X6)) )),
% 0.22/0.43    inference(forward_demodulation,[],[f81,f26])).
% 0.22/0.43  fof(f81,plain,(
% 0.22/0.43    ( ! [X6,X4,X5] : (k1_xboole_0 != k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,k2_xboole_0(X5,X6))) | r1_xboole_0(k4_xboole_0(X4,X5),X6)) )),
% 0.22/0.43    inference(superposition,[],[f29,f26])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f23,f21])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.43    inference(nnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (4195)------------------------------
% 0.22/0.43  % (4195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (4195)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (4195)Memory used [KB]: 2302
% 0.22/0.43  % (4195)Time elapsed: 0.024 s
% 0.22/0.43  % (4195)------------------------------
% 0.22/0.43  % (4195)------------------------------
% 0.22/0.44  % (4182)Success in time 0.076 s
%------------------------------------------------------------------------------
