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
% DateTime   : Thu Dec  3 12:34:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f15])).

fof(f15,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f9,f14])).

fof(f14,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f10,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f11,f12])).

fof(f12,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f11,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).

fof(f10,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f9,plain,(
    k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).

fof(f7,plain,
    ( ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0)
   => k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:07:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (26223)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.42  % (26223)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(trivial_inequality_removal,[],[f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.42    inference(definition_unfolding,[],[f9,f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.42    inference(definition_unfolding,[],[f10,f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.42    inference(definition_unfolding,[],[f11,f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0) => k1_tarski(sK0) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f6,plain,(
% 0.22/0.43    ? [X0] : k1_tarski(X0) != k4_enumset1(X0,X0,X0,X0,X0,X0)),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,negated_conjecture,(
% 0.22/0.43    ~! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)),
% 0.22/0.43    inference(negated_conjecture,[],[f4])).
% 0.22/0.43  fof(f4,conjecture,(
% 0.22/0.43    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_enumset1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (26223)------------------------------
% 0.22/0.43  % (26223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (26223)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (26223)Memory used [KB]: 1535
% 0.22/0.43  % (26223)Time elapsed: 0.003 s
% 0.22/0.43  % (26223)------------------------------
% 0.22/0.43  % (26223)------------------------------
% 0.22/0.43  % (26210)Success in time 0.062 s
%------------------------------------------------------------------------------
