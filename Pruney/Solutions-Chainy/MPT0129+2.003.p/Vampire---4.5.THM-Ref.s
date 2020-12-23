%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(subsumption_resolution,[],[f11,f29])).

fof(f29,plain,(
    ! [X6,X4,X7,X5] : k2_xboole_0(k2_tarski(X7,X4),k2_tarski(X5,X6)) = k2_enumset1(X7,X4,X5,X6) ),
    inference(forward_demodulation,[],[f24,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f24,plain,(
    ! [X6,X4,X7,X5] : k2_xboole_0(k2_tarski(X7,X4),k2_tarski(X5,X6)) = k2_xboole_0(k1_tarski(X7),k1_enumset1(X4,X5,X6)) ),
    inference(superposition,[],[f17,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(superposition,[],[f15,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f11,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.43  % (15191)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.43  % (15191)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(subsumption_resolution,[],[f11,f29])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k2_tarski(X7,X4),k2_tarski(X5,X6)) = k2_enumset1(X7,X4,X5,X6)) )),
% 0.22/0.43    inference(forward_demodulation,[],[f24,f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k2_tarski(X7,X4),k2_tarski(X5,X6)) = k2_xboole_0(k1_tarski(X7),k1_enumset1(X4,X5,X6))) )),
% 0.22/0.43    inference(superposition,[],[f17,f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.22/0.43    inference(superposition,[],[f15,f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.43    inference(negated_conjecture,[],[f6])).
% 0.22/0.43  fof(f6,conjecture,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (15191)------------------------------
% 0.22/0.43  % (15191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (15191)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (15191)Memory used [KB]: 6140
% 0.22/0.43  % (15191)Time elapsed: 0.004 s
% 0.22/0.43  % (15191)------------------------------
% 0.22/0.43  % (15191)------------------------------
% 0.22/0.43  % (15174)Success in time 0.073 s
%------------------------------------------------------------------------------
