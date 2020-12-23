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
% DateTime   : Thu Dec  3 12:34:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   14 (  18 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   15 (  19 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f13])).

fof(f13,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(forward_demodulation,[],[f12,f9])).

fof(f9,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f12,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK3)) ),
    inference(forward_demodulation,[],[f11,f9])).

fof(f11,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK3,sK2)) ),
    inference(definition_unfolding,[],[f8,f10,f10])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f8,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X3,X2)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X3,X2) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X3,X2) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:30:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (26241)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (26241)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(trivial_inequality_removal,[],[f13])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.22/0.46    inference(forward_demodulation,[],[f12,f9])).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK3))),
% 0.22/0.46    inference(forward_demodulation,[],[f11,f9])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK3,sK2))),
% 0.22/0.46    inference(definition_unfolding,[],[f8,f10,f10])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.22/0.46  fof(f8,plain,(
% 0.22/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2)),
% 0.22/0.46    inference(cnf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,plain,(
% 0.22/0.46    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).
% 0.22/0.46  fof(f6,plain,(
% 0.22/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X3,X2) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK3,sK2)),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f5,plain,(
% 0.22/0.46    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X3,X2)),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X3,X2)),
% 0.22/0.46    inference(negated_conjecture,[],[f3])).
% 0.22/0.46  fof(f3,conjecture,(
% 0.22/0.46    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X3,X2)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_enumset1)).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (26241)------------------------------
% 0.22/0.46  % (26241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (26241)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (26241)Memory used [KB]: 6012
% 0.22/0.46  % (26241)Time elapsed: 0.003 s
% 0.22/0.46  % (26241)------------------------------
% 0.22/0.46  % (26241)------------------------------
% 0.22/0.46  % (26234)Success in time 0.102 s
%------------------------------------------------------------------------------
