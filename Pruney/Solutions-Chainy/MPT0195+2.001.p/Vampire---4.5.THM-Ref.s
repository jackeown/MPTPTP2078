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
% DateTime   : Thu Dec  3 12:34:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  29 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :   20 (  30 expanded)
%              Number of equality atoms :   19 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f28])).

fof(f28,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(forward_demodulation,[],[f27,f10])).

fof(f10,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f27,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK3)) ),
    inference(forward_demodulation,[],[f26,f10])).

fof(f26,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK3,sK2)) ),
    inference(superposition,[],[f15,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X0,X2),k2_tarski(X3,X1)) ),
    inference(definition_unfolding,[],[f11,f12,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(f15,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK3)) ),
    inference(forward_demodulation,[],[f13,f10])).

fof(f13,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK2,sK1),k2_tarski(sK0,sK3)) ),
    inference(definition_unfolding,[],[f9,f12,f12])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.40  % (25377)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.40  % (25377)Refutation found. Thanks to Tanya!
% 0.20/0.40  % SZS status Theorem for theBenchmark
% 0.20/0.40  % SZS output start Proof for theBenchmark
% 0.20/0.40  fof(f29,plain,(
% 0.20/0.40    $false),
% 0.20/0.40    inference(trivial_inequality_removal,[],[f28])).
% 0.20/0.40  fof(f28,plain,(
% 0.20/0.40    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.20/0.40    inference(forward_demodulation,[],[f27,f10])).
% 0.20/0.40  fof(f10,plain,(
% 0.20/0.40    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f1])).
% 0.20/0.40  fof(f1,axiom,(
% 0.20/0.40    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.40  fof(f27,plain,(
% 0.20/0.40    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK3))),
% 0.20/0.40    inference(forward_demodulation,[],[f26,f10])).
% 0.20/0.40  fof(f26,plain,(
% 0.20/0.40    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK3,sK2))),
% 0.20/0.40    inference(superposition,[],[f15,f14])).
% 0.20/0.40  fof(f14,plain,(
% 0.20/0.40    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X0,X2),k2_tarski(X3,X1))) )),
% 0.20/0.40    inference(definition_unfolding,[],[f11,f12,f12])).
% 0.20/0.40  fof(f12,plain,(
% 0.20/0.40    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.20/0.40    inference(cnf_transformation,[],[f2])).
% 0.20/0.40  fof(f2,axiom,(
% 0.20/0.40    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.20/0.40  fof(f11,plain,(
% 0.20/0.40    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f3])).
% 0.20/0.40  fof(f3,axiom,(
% 0.20/0.40    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).
% 0.20/0.40  fof(f15,plain,(
% 0.20/0.40    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK3))),
% 0.20/0.40    inference(forward_demodulation,[],[f13,f10])).
% 0.20/0.40  fof(f13,plain,(
% 0.20/0.40    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK2,sK1),k2_tarski(sK0,sK3))),
% 0.20/0.40    inference(definition_unfolding,[],[f9,f12,f12])).
% 0.20/0.40  fof(f9,plain,(
% 0.20/0.40    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)),
% 0.20/0.40    inference(cnf_transformation,[],[f8])).
% 0.20/0.40  fof(f8,plain,(
% 0.20/0.40    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)),
% 0.20/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f7])).
% 0.20/0.40  fof(f7,plain,(
% 0.20/0.40    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK0,sK3)),
% 0.20/0.40    introduced(choice_axiom,[])).
% 0.20/0.40  fof(f6,plain,(
% 0.20/0.40    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X0,X3)),
% 0.20/0.40    inference(ennf_transformation,[],[f5])).
% 0.20/0.40  fof(f5,negated_conjecture,(
% 0.20/0.40    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 0.20/0.40    inference(negated_conjecture,[],[f4])).
% 0.20/0.40  fof(f4,conjecture,(
% 0.20/0.40    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_enumset1)).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (25377)------------------------------
% 0.20/0.41  % (25377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (25377)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (25377)Memory used [KB]: 6012
% 0.20/0.41  % (25377)Time elapsed: 0.004 s
% 0.20/0.41  % (25377)------------------------------
% 0.20/0.41  % (25377)------------------------------
% 0.20/0.41  % (25374)Success in time 0.055 s
%------------------------------------------------------------------------------
