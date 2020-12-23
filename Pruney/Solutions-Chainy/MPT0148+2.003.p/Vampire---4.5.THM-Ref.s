%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   23 (  30 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  31 expanded)
%              Number of equality atoms :   23 (  30 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19,f90])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_enumset1(X6,X7,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k6_enumset1(X6,X7,X0,X1,X2,X3,X4,X5) ),
    inference(forward_demodulation,[],[f87,f32])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_enumset1(X6,X7,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k2_tarski(X6,X7),k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(superposition,[],[f45,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_enumset1(X3,X0,X1),X2) ),
    inference(forward_demodulation,[],[f40,f34])).

fof(f34,plain,(
    ! [X6,X4,X5,X3] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6) ),
    inference(superposition,[],[f22,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2)) ),
    inference(superposition,[],[f33,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(superposition,[],[f22,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f19,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:54:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (32695)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.45  % (32695)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f91,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(subsumption_resolution,[],[f19,f90])).
% 0.22/0.45  fof(f90,plain,(
% 0.22/0.45    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X6,X7,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k6_enumset1(X6,X7,X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.45    inference(forward_demodulation,[],[f87,f32])).
% 0.22/0.45  fof(f32,plain,(
% 0.22/0.45    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).
% 0.22/0.45  fof(f87,plain,(
% 0.22/0.45    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X6,X7,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k2_tarski(X6,X7),k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 0.22/0.45    inference(superposition,[],[f45,f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,axiom,(
% 0.22/0.45    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_enumset1(X3,X0,X1),X2)) )),
% 0.22/0.45    inference(forward_demodulation,[],[f40,f34])).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6)) )),
% 0.22/0.45    inference(superposition,[],[f22,f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X3,X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X0,X1),X2))) )),
% 0.22/0.45    inference(superposition,[],[f33,f33])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.22/0.45    inference(superposition,[],[f22,f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f16,f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k3_enumset1(sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))),
% 0.22/0.45    inference(ennf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))),
% 0.22/0.45    inference(negated_conjecture,[],[f14])).
% 0.22/0.45  fof(f14,conjecture,(
% 0.22/0.45    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (32695)------------------------------
% 0.22/0.45  % (32695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (32695)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (32695)Memory used [KB]: 6140
% 0.22/0.45  % (32695)Time elapsed: 0.036 s
% 0.22/0.45  % (32695)------------------------------
% 0.22/0.45  % (32695)------------------------------
% 0.22/0.46  % (32675)Success in time 0.097 s
%------------------------------------------------------------------------------
