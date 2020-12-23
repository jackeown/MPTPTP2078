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
% DateTime   : Thu Dec  3 12:34:03 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   24 (  39 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :   25 (  40 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f23])).

fof(f23,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(superposition,[],[f22,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2)) ),
    inference(definition_unfolding,[],[f13,f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(f13,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).

fof(f22,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f21,f19])).

fof(f21,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f20,f19])).

fof(f20,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2))) ),
    inference(definition_unfolding,[],[f11,f18])).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)),k2_xboole_0(k1_enumset1(X4,X4,X4),k1_enumset1(X5,X6,X7))) ),
    inference(definition_unfolding,[],[f16,f17,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)) ),
    inference(definition_unfolding,[],[f14,f12])).

fof(f12,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_enumset1)).

fof(f11,plain,(
    k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % WCLimit    : 600
% 0.15/0.37  % DateTime   : Tue Dec  1 10:59:15 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.23/0.46  % (3181)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.23/0.46  % (3177)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.46  % (3176)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.46  % (3176)Refutation found. Thanks to Tanya!
% 0.23/0.46  % SZS status Theorem for theBenchmark
% 0.23/0.46  % SZS output start Proof for theBenchmark
% 0.23/0.46  fof(f24,plain,(
% 0.23/0.46    $false),
% 0.23/0.46    inference(trivial_inequality_removal,[],[f23])).
% 0.23/0.46  fof(f23,plain,(
% 0.23/0.46    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)),
% 0.23/0.46    inference(superposition,[],[f22,f19])).
% 0.23/0.46  fof(f19,plain,(
% 0.23/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2))) )),
% 0.23/0.46    inference(definition_unfolding,[],[f13,f15])).
% 0.23/0.46  fof(f15,plain,(
% 0.23/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.23/0.46    inference(cnf_transformation,[],[f1])).
% 0.23/0.46  fof(f1,axiom,(
% 0.23/0.46    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.23/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).
% 0.23/0.46  fof(f13,plain,(
% 0.23/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.23/0.46    inference(cnf_transformation,[],[f5])).
% 0.23/0.46  fof(f5,axiom,(
% 0.23/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 0.23/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).
% 0.23/0.46  fof(f22,plain,(
% 0.23/0.46    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2))),
% 0.23/0.46    inference(forward_demodulation,[],[f21,f19])).
% 0.23/0.46  fof(f21,plain,(
% 0.23/0.46    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK1,sK2))),
% 0.23/0.46    inference(forward_demodulation,[],[f20,f19])).
% 0.23/0.46  fof(f20,plain,(
% 0.23/0.46    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0)),k2_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2)))),
% 0.23/0.46    inference(definition_unfolding,[],[f11,f18])).
% 0.23/0.46  fof(f18,plain,(
% 0.23/0.46    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)),k2_xboole_0(k1_enumset1(X4,X4,X4),k1_enumset1(X5,X6,X7)))) )),
% 0.23/0.46    inference(definition_unfolding,[],[f16,f17,f17])).
% 0.23/0.46  fof(f17,plain,(
% 0.23/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) )),
% 0.23/0.46    inference(definition_unfolding,[],[f14,f12])).
% 0.23/0.46  fof(f12,plain,(
% 0.23/0.46    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.23/0.46    inference(cnf_transformation,[],[f4])).
% 0.23/0.46  fof(f4,axiom,(
% 0.23/0.46    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0)),
% 0.23/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 0.23/0.46  fof(f14,plain,(
% 0.23/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.23/0.46    inference(cnf_transformation,[],[f2])).
% 0.23/0.46  fof(f2,axiom,(
% 0.23/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.23/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.23/0.46  fof(f16,plain,(
% 0.23/0.46    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 0.23/0.46    inference(cnf_transformation,[],[f3])).
% 0.23/0.46  fof(f3,axiom,(
% 0.23/0.46    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 0.23/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_enumset1)).
% 0.23/0.46  fof(f11,plain,(
% 0.23/0.46    k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.23/0.46    inference(cnf_transformation,[],[f10])).
% 0.23/0.46  fof(f10,plain,(
% 0.23/0.46    k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.23/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).
% 0.23/0.46  fof(f9,plain,(
% 0.23/0.46    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.23/0.46    introduced(choice_axiom,[])).
% 0.23/0.46  fof(f8,plain,(
% 0.23/0.46    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)),
% 0.23/0.46    inference(ennf_transformation,[],[f7])).
% 0.23/0.46  fof(f7,negated_conjecture,(
% 0.23/0.46    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)),
% 0.23/0.46    inference(negated_conjecture,[],[f6])).
% 0.23/0.46  fof(f6,conjecture,(
% 0.23/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)),
% 0.23/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_enumset1)).
% 0.23/0.46  % SZS output end Proof for theBenchmark
% 0.23/0.46  % (3176)------------------------------
% 0.23/0.46  % (3176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.46  % (3176)Termination reason: Refutation
% 0.23/0.46  
% 0.23/0.46  % (3176)Memory used [KB]: 6012
% 0.23/0.46  % (3176)Time elapsed: 0.051 s
% 0.23/0.46  % (3176)------------------------------
% 0.23/0.46  % (3176)------------------------------
% 0.23/0.46  % (3173)Success in time 0.079 s
%------------------------------------------------------------------------------
