%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  44 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :   24 (  45 expanded)
%              Number of equality atoms :   23 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f72])).

fof(f72,plain,(
    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f44,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X3,X2,X1) ),
    inference(definition_unfolding,[],[f13,f14,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f13,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).

fof(f44,plain,(
    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK3,sK2,sK1) ),
    inference(superposition,[],[f36,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X1,X1,X2,X0,X3) ),
    inference(definition_unfolding,[],[f11,f14,f14])).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).

fof(f36,plain,(
    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK2,sK2,sK0,sK3,sK1) ),
    inference(superposition,[],[f22,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X3,X1) ),
    inference(definition_unfolding,[],[f12,f14,f14])).

fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(f22,plain,(
    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK2,sK2,sK3,sK1,sK0) ),
    inference(superposition,[],[f15,f16])).

fof(f15,plain,(
    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK3,sK3,sK1,sK2,sK0) ),
    inference(definition_unfolding,[],[f10,f14,f14])).

fof(f10,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK1,sK2,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X1,X2,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK1,sK2,sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X1,X2,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:12:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.43  % (13262)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.43  % (13262)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(trivial_inequality_removal,[],[f72])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.20/0.43    inference(superposition,[],[f44,f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X3,X2,X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f13,f14,f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_enumset1)).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK3,sK2,sK1)),
% 0.20/0.43    inference(superposition,[],[f36,f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X1,X1,X2,X0,X3)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f11,f14,f14])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK2,sK2,sK0,sK3,sK1)),
% 0.20/0.43    inference(superposition,[],[f22,f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X0,X2,X3,X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f12,f14,f14])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK2,sK2,sK3,sK1,sK0)),
% 0.20/0.43    inference(superposition,[],[f15,f16])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK3,sK3,sK1,sK2,sK0)),
% 0.20/0.43    inference(definition_unfolding,[],[f10,f14,f14])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK1,sK2,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK1,sK2,sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X1,X2,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK1,sK2,sK0)),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X1,X2,X0)),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)),
% 0.20/0.43    inference(negated_conjecture,[],[f5])).
% 0.20/0.43  fof(f5,conjecture,(
% 0.20/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X1,X2,X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_enumset1)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (13262)------------------------------
% 0.20/0.43  % (13262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (13262)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (13262)Memory used [KB]: 1663
% 0.20/0.43  % (13262)Time elapsed: 0.006 s
% 0.20/0.43  % (13262)------------------------------
% 0.20/0.43  % (13262)------------------------------
% 0.20/0.43  % (13249)Success in time 0.075 s
%------------------------------------------------------------------------------
