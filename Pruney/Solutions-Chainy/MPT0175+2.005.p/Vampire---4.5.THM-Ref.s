%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:00 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f18])).

fof(f18,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f10,f17])).

fof(f17,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f11,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f12,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f13,f14])).

fof(f14,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f13,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).

fof(f12,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f11,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f10,plain,(
    k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f8])).

fof(f8,plain,
    ( ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0)
   => k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.41  % (24003)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.44  % (24003)Refutation found. Thanks to Tanya!
% 0.19/0.44  % SZS status Theorem for theBenchmark
% 0.19/0.44  % SZS output start Proof for theBenchmark
% 0.19/0.44  fof(f19,plain,(
% 0.19/0.44    $false),
% 0.19/0.44    inference(trivial_inequality_removal,[],[f18])).
% 0.19/0.44  fof(f18,plain,(
% 0.19/0.44    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.19/0.44    inference(definition_unfolding,[],[f10,f17])).
% 0.19/0.44  fof(f17,plain,(
% 0.19/0.44    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.19/0.44    inference(definition_unfolding,[],[f11,f16])).
% 0.19/0.44  fof(f16,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.19/0.44    inference(definition_unfolding,[],[f12,f15])).
% 0.19/0.44  fof(f15,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.19/0.44    inference(definition_unfolding,[],[f13,f14])).
% 0.19/0.44  fof(f14,plain,(
% 0.19/0.44    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f3])).
% 0.19/0.44  fof(f3,axiom,(
% 0.19/0.44    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.44  fof(f13,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f4])).
% 0.19/0.44  fof(f4,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).
% 0.19/0.44  fof(f12,plain,(
% 0.19/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f2])).
% 0.19/0.44  fof(f2,axiom,(
% 0.19/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.44  fof(f11,plain,(
% 0.19/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f1])).
% 0.19/0.44  fof(f1,axiom,(
% 0.19/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.44  fof(f10,plain,(
% 0.19/0.44    k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.19/0.44    inference(cnf_transformation,[],[f9])).
% 0.19/0.44  fof(f9,plain,(
% 0.19/0.44    k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f8])).
% 0.19/0.44  fof(f8,plain,(
% 0.19/0.44    ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0) => k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f7,plain,(
% 0.19/0.44    ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0)),
% 0.19/0.44    inference(ennf_transformation,[],[f6])).
% 0.19/0.44  fof(f6,negated_conjecture,(
% 0.19/0.44    ~! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)),
% 0.19/0.44    inference(negated_conjecture,[],[f5])).
% 0.19/0.44  fof(f5,conjecture,(
% 0.19/0.44    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)),
% 0.19/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_enumset1)).
% 0.19/0.44  % SZS output end Proof for theBenchmark
% 0.19/0.44  % (24003)------------------------------
% 0.19/0.44  % (24003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (24003)Termination reason: Refutation
% 0.19/0.44  
% 0.19/0.44  % (24003)Memory used [KB]: 6012
% 0.19/0.44  % (24003)Time elapsed: 0.030 s
% 0.19/0.44  % (24003)------------------------------
% 0.19/0.44  % (24003)------------------------------
% 0.19/0.44  % (23992)Success in time 0.09 s
%------------------------------------------------------------------------------
