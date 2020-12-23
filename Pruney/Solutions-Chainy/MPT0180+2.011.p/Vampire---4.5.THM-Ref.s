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
% DateTime   : Thu Dec  3 12:34:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f18])).

fof(f18,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f10,f17])).

fof(f17,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f11,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f12,f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f13,f14])).

fof(f14,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).

fof(f12,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f11,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

fof(f10,plain,(
    k1_tarski(sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_tarski(sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f8])).

fof(f8,plain,
    ( ? [X0] : k1_tarski(X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
   => k1_tarski(sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : k1_tarski(X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.40  % (31821)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.40  % (31821)Refutation found. Thanks to Tanya!
% 0.20/0.40  % SZS status Theorem for theBenchmark
% 0.20/0.40  % SZS output start Proof for theBenchmark
% 0.20/0.40  fof(f19,plain,(
% 0.20/0.40    $false),
% 0.20/0.40    inference(trivial_inequality_removal,[],[f18])).
% 0.20/0.40  fof(f18,plain,(
% 0.20/0.40    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.40    inference(definition_unfolding,[],[f10,f17])).
% 0.20/0.40  fof(f17,plain,(
% 0.20/0.40    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.40    inference(definition_unfolding,[],[f11,f16])).
% 0.20/0.40  fof(f16,plain,(
% 0.20/0.40    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.40    inference(definition_unfolding,[],[f12,f15])).
% 0.20/0.40  fof(f15,plain,(
% 0.20/0.40    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.40    inference(definition_unfolding,[],[f13,f14])).
% 0.20/0.40  fof(f14,plain,(
% 0.20/0.40    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f4])).
% 0.20/0.40  fof(f4,axiom,(
% 0.20/0.40    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).
% 0.20/0.40  fof(f13,plain,(
% 0.20/0.40    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f3])).
% 0.20/0.40  fof(f3,axiom,(
% 0.20/0.40    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_enumset1)).
% 0.20/0.40  fof(f12,plain,(
% 0.20/0.40    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f1])).
% 0.20/0.40  fof(f1,axiom,(
% 0.20/0.40    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.40  fof(f11,plain,(
% 0.20/0.40    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f2])).
% 0.20/0.40  fof(f2,axiom,(
% 0.20/0.40    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).
% 0.20/0.40  fof(f10,plain,(
% 0.20/0.40    k1_tarski(sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.40    inference(cnf_transformation,[],[f9])).
% 0.20/0.40  fof(f9,plain,(
% 0.20/0.40    k1_tarski(sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f8])).
% 0.20/0.40  fof(f8,plain,(
% 0.20/0.40    ? [X0] : k1_tarski(X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) => k1_tarski(sK0) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.20/0.40    introduced(choice_axiom,[])).
% 0.20/0.40  fof(f7,plain,(
% 0.20/0.40    ? [X0] : k1_tarski(X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),
% 0.20/0.40    inference(ennf_transformation,[],[f6])).
% 0.20/0.40  fof(f6,negated_conjecture,(
% 0.20/0.40    ~! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),
% 0.20/0.40    inference(negated_conjecture,[],[f5])).
% 0.20/0.40  fof(f5,conjecture,(
% 0.20/0.40    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_enumset1)).
% 0.20/0.40  % SZS output end Proof for theBenchmark
% 0.20/0.40  % (31821)------------------------------
% 0.20/0.40  % (31821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.40  % (31821)Termination reason: Refutation
% 0.20/0.40  
% 0.20/0.40  % (31821)Memory used [KB]: 1535
% 0.20/0.40  % (31821)Time elapsed: 0.002 s
% 0.20/0.40  % (31821)------------------------------
% 0.20/0.40  % (31821)------------------------------
% 0.20/0.41  % (31807)Success in time 0.057 s
%------------------------------------------------------------------------------
