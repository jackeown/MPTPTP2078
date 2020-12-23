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
% DateTime   : Thu Dec  3 12:34:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 ( 133 expanded)
%              Number of leaves         :    8 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   29 ( 134 expanded)
%              Number of equality atoms :   28 ( 133 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(subsumption_resolution,[],[f73,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X3,X1) ),
    inference(definition_unfolding,[],[f15,f25,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f19,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(f73,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK3,sK1,sK2) ),
    inference(superposition,[],[f58,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X2,X2,X2,X2,X2,X3,X1,X0) ),
    inference(definition_unfolding,[],[f17,f25,f25])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_enumset1)).

fof(f58,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK1,sK0,sK3) ),
    inference(superposition,[],[f34,f29])).

fof(f34,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK0,sK2,sK1) ),
    inference(superposition,[],[f26,f27])).

fof(f26,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK1,sK0) ),
    inference(definition_unfolding,[],[f14,f25,f25])).

fof(f14,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:49:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (19481)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.41  % (19481)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f75,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(subsumption_resolution,[],[f73,f27])).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X3,X1)) )),
% 0.21/0.41    inference(definition_unfolding,[],[f15,f25,f25])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.41    inference(definition_unfolding,[],[f19,f24])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.41    inference(definition_unfolding,[],[f20,f23])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.41    inference(definition_unfolding,[],[f21,f22])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,axiom,(
% 0.21/0.41    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f7])).
% 0.21/0.41  fof(f7,axiom,(
% 0.21/0.41    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,axiom,(
% 0.21/0.41    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).
% 0.21/0.41  fof(f73,plain,(
% 0.21/0.41    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK3,sK1,sK2)),
% 0.21/0.41    inference(superposition,[],[f58,f29])).
% 0.21/0.41  fof(f29,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X2,X2,X2,X2,X2,X3,X1,X0)) )),
% 0.21/0.41    inference(definition_unfolding,[],[f17,f25,f25])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_enumset1)).
% 0.21/0.41  fof(f58,plain,(
% 0.21/0.41    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK1,sK0,sK3)),
% 0.21/0.41    inference(superposition,[],[f34,f29])).
% 0.21/0.41  fof(f34,plain,(
% 0.21/0.41    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK0,sK2,sK1)),
% 0.21/0.41    inference(superposition,[],[f26,f27])).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK2,sK1,sK0)),
% 0.21/0.41    inference(definition_unfolding,[],[f14,f25,f25])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)),
% 0.21/0.41    inference(ennf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.21/0.41    inference(negated_conjecture,[],[f9])).
% 0.21/0.41  fof(f9,conjecture,(
% 0.21/0.41    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (19481)------------------------------
% 0.21/0.41  % (19481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (19481)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (19481)Memory used [KB]: 1663
% 0.21/0.41  % (19481)Time elapsed: 0.005 s
% 0.21/0.41  % (19481)------------------------------
% 0.21/0.41  % (19481)------------------------------
% 0.21/0.42  % (19468)Success in time 0.058 s
%------------------------------------------------------------------------------
