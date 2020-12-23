%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    7
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f12])).

fof(f12,plain,(
    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) ),
    inference(superposition,[],[f11,f9])).

fof(f9,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f11,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(superposition,[],[f8,f10])).

fof(f10,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f8,plain,(
    k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_enumset1(X0,X0,X0,X1)
   => k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_enumset1(X0,X0,X0,X1) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (17416)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.45  % (17416)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)),
% 0.21/0.45    inference(superposition,[],[f11,f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.21/0.45    inference(superposition,[],[f8,f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,plain,(
% 0.21/0.45    k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).
% 0.21/0.45  fof(f6,plain,(
% 0.21/0.45    ? [X0,X1] : k2_tarski(X0,X1) != k2_enumset1(X0,X0,X0,X1) => k2_tarski(sK0,sK1) != k2_enumset1(sK0,sK0,sK0,sK1)),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f5,plain,(
% 0.21/0.45    ? [X0,X1] : k2_tarski(X0,X1) != k2_enumset1(X0,X0,X0,X1)),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 0.21/0.45    inference(negated_conjecture,[],[f3])).
% 0.21/0.45  fof(f3,conjecture,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (17416)------------------------------
% 0.21/0.45  % (17416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (17416)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (17416)Memory used [KB]: 6012
% 0.21/0.45  % (17416)Time elapsed: 0.027 s
% 0.21/0.45  % (17416)------------------------------
% 0.21/0.45  % (17416)------------------------------
% 0.21/0.45  % (17397)Success in time 0.092 s
%------------------------------------------------------------------------------
