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
% DateTime   : Thu Dec  3 12:34:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
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
fof(f27,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f26])).

fof(f26,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(superposition,[],[f15,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X1,X3),k2_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f11,f12,f12])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

fof(f15,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK3),k2_tarski(sK0,sK2)) ),
    inference(backward_demodulation,[],[f13,f10])).

fof(f10,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f13,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK3),k2_tarski(sK2,sK0)) ),
    inference(definition_unfolding,[],[f9,f12,f12])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 19:40:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.41  % (12638)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.42  % (12638)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.21/0.42    inference(superposition,[],[f15,f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X1,X3),k2_tarski(X0,X2))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f11,f12,f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK3),k2_tarski(sK0,sK2))),
% 0.21/0.42    inference(backward_demodulation,[],[f13,f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK3),k2_tarski(sK2,sK0))),
% 0.21/0.42    inference(definition_unfolding,[],[f9,f12,f12])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X2,X0)),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.21/0.42    inference(negated_conjecture,[],[f4])).
% 0.21/0.42  fof(f4,conjecture,(
% 0.21/0.42    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (12638)------------------------------
% 0.21/0.42  % (12638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (12638)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (12638)Memory used [KB]: 10618
% 0.21/0.42  % (12638)Time elapsed: 0.004 s
% 0.21/0.42  % (12638)------------------------------
% 0.21/0.42  % (12638)------------------------------
% 0.21/0.42  % (12622)Success in time 0.062 s
%------------------------------------------------------------------------------
