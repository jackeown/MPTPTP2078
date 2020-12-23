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
% DateTime   : Thu Dec  3 12:33:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   20 (  24 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   21 (  25 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :   11 (   7 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(subsumption_resolution,[],[f11,f146])).

fof(f146,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X6,X7,X0,X1,X2,X3),k2_tarski(X4,X5)) = k6_enumset1(X6,X7,X0,X1,X2,X3,X4,X5) ),
    inference(forward_demodulation,[],[f142,f16])).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

fof(f142,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X6,X7,X0,X1,X2,X3),k2_tarski(X4,X5)) = k2_xboole_0(k2_tarski(X6,X7),k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(superposition,[],[f88,f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X4,X5),k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X6)) = k2_xboole_0(k4_enumset1(X4,X5,X0,X1,X2,X3),X6) ),
    inference(forward_demodulation,[],[f80,f15])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k2_enumset1(X4,X5,X0,X1),k2_tarski(X2,X3)),X6) = k2_xboole_0(k2_tarski(X4,X5),k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X6)) ),
    inference(superposition,[],[f18,f13])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f18,plain,(
    ! [X6,X4,X8,X7,X5,X9] : k2_xboole_0(k2_tarski(X4,X5),k2_xboole_0(k2_xboole_0(k2_tarski(X6,X7),X8),X9)) = k2_xboole_0(k2_xboole_0(k2_enumset1(X4,X5,X6,X7),X8),X9) ),
    inference(superposition,[],[f14,f13])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).

fof(f11,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:58:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (516)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (515)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (515)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f11,f146])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X6,X7,X0,X1,X2,X3),k2_tarski(X4,X5)) = k6_enumset1(X6,X7,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f142,f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X6,X7,X0,X1,X2,X3),k2_tarski(X4,X5)) = k2_xboole_0(k2_tarski(X6,X7),k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 0.22/0.49    inference(superposition,[],[f88,f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X4,X5),k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X6)) = k2_xboole_0(k4_enumset1(X4,X5,X0,X1,X2,X3),X6)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f80,f15])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_enumset1(X4,X5,X0,X1),k2_tarski(X2,X3)),X6) = k2_xboole_0(k2_tarski(X4,X5),k2_xboole_0(k2_enumset1(X0,X1,X2,X3),X6))) )),
% 0.22/0.49    inference(superposition,[],[f18,f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X6,X4,X8,X7,X5,X9] : (k2_xboole_0(k2_tarski(X4,X5),k2_xboole_0(k2_xboole_0(k2_tarski(X6,X7),X8),X9)) = k2_xboole_0(k2_xboole_0(k2_enumset1(X4,X5,X6,X7),X8),X9)) )),
% 0.22/0.49    inference(superposition,[],[f14,f13])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.22/0.49    inference(negated_conjecture,[],[f6])).
% 0.22/0.49  fof(f6,conjecture,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (515)------------------------------
% 0.22/0.49  % (515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (515)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (515)Memory used [KB]: 6268
% 0.22/0.49  % (515)Time elapsed: 0.064 s
% 0.22/0.49  % (515)------------------------------
% 0.22/0.49  % (515)------------------------------
% 0.22/0.49  % (493)Success in time 0.132 s
%------------------------------------------------------------------------------
