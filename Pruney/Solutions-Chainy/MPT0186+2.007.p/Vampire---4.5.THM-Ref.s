%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:15 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   17 (  23 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   18 (  24 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f23])).

fof(f23,plain,(
    k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) ),
    inference(superposition,[],[f17,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X3,X2)) ),
    inference(definition_unfolding,[],[f11,f12,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

fof(f17,plain,(
    k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK3,sK2)) ),
    inference(forward_demodulation,[],[f13,f10])).

fof(f10,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).

fof(f13,plain,(
    k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK2,sK1,sK3)) ),
    inference(definition_unfolding,[],[f9,f12,f12])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (13370)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.13/0.42  % (13370)Refutation found. Thanks to Tanya!
% 0.13/0.42  % SZS status Theorem for theBenchmark
% 0.13/0.42  % SZS output start Proof for theBenchmark
% 0.13/0.42  fof(f24,plain,(
% 0.13/0.42    $false),
% 0.13/0.42    inference(trivial_inequality_removal,[],[f23])).
% 0.13/0.42  fof(f23,plain,(
% 0.13/0.42    k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3))),
% 0.13/0.42    inference(superposition,[],[f17,f14])).
% 0.13/0.42  fof(f14,plain,(
% 0.13/0.42    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X3,X2))) )),
% 0.13/0.42    inference(definition_unfolding,[],[f11,f12,f12])).
% 0.13/0.42  fof(f12,plain,(
% 0.13/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f3])).
% 0.13/0.42  fof(f3,axiom,(
% 0.13/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.13/0.42  fof(f11,plain,(
% 0.13/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f2])).
% 0.13/0.42  fof(f2,axiom,(
% 0.13/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).
% 0.13/0.42  fof(f17,plain,(
% 0.13/0.42    k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK3,sK2))),
% 0.13/0.42    inference(forward_demodulation,[],[f13,f10])).
% 0.13/0.42  fof(f10,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f1])).
% 0.13/0.42  fof(f1,axiom,(
% 0.13/0.42    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_enumset1)).
% 0.13/0.42  fof(f13,plain,(
% 0.13/0.42    k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK2,sK1,sK3))),
% 0.13/0.42    inference(definition_unfolding,[],[f9,f12,f12])).
% 0.13/0.42  fof(f9,plain,(
% 0.13/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.13/0.42    inference(cnf_transformation,[],[f8])).
% 0.13/0.42  fof(f8,plain,(
% 0.13/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.13/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f7])).
% 0.13/0.42  fof(f7,plain,(
% 0.13/0.42    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.13/0.42    introduced(choice_axiom,[])).
% 0.13/0.42  fof(f6,plain,(
% 0.13/0.42    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3)),
% 0.13/0.42    inference(ennf_transformation,[],[f5])).
% 0.13/0.42  fof(f5,negated_conjecture,(
% 0.13/0.42    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 0.13/0.42    inference(negated_conjecture,[],[f4])).
% 0.13/0.42  fof(f4,conjecture,(
% 0.13/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).
% 0.13/0.42  % SZS output end Proof for theBenchmark
% 0.13/0.42  % (13370)------------------------------
% 0.13/0.42  % (13370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.42  % (13370)Termination reason: Refutation
% 0.13/0.42  
% 0.13/0.42  % (13370)Memory used [KB]: 1535
% 0.13/0.42  % (13370)Time elapsed: 0.004 s
% 0.13/0.42  % (13370)------------------------------
% 0.13/0.42  % (13370)------------------------------
% 0.13/0.42  % (13357)Success in time 0.063 s
%------------------------------------------------------------------------------
