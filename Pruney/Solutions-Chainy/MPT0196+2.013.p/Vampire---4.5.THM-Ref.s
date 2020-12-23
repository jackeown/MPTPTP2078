%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    5
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8,f17])).

fof(f17,plain,(
    ! [X10,X8,X11,X9] : k2_enumset1(X9,X8,X10,X11) = k2_enumset1(X11,X8,X9,X10) ),
    inference(superposition,[],[f10,f9])).

fof(f9,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_enumset1)).

fof(f8,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:06:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.40  % (22363)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.40  % (22363)Refutation found. Thanks to Tanya!
% 0.22/0.40  % SZS status Theorem for theBenchmark
% 0.22/0.40  % SZS output start Proof for theBenchmark
% 0.22/0.40  fof(f25,plain,(
% 0.22/0.40    $false),
% 0.22/0.40    inference(subsumption_resolution,[],[f8,f17])).
% 0.22/0.40  fof(f17,plain,(
% 0.22/0.40    ( ! [X10,X8,X11,X9] : (k2_enumset1(X9,X8,X10,X11) = k2_enumset1(X11,X8,X9,X10)) )),
% 0.22/0.40    inference(superposition,[],[f10,f9])).
% 0.22/0.40  fof(f9,plain,(
% 0.22/0.40    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)) )),
% 0.22/0.40    inference(cnf_transformation,[],[f1])).
% 0.22/0.40  fof(f1,axiom,(
% 0.22/0.40    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 0.22/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
% 0.22/0.40  fof(f10,plain,(
% 0.22/0.40    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)) )),
% 0.22/0.40    inference(cnf_transformation,[],[f2])).
% 0.22/0.40  fof(f2,axiom,(
% 0.22/0.40    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)),
% 0.22/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_enumset1)).
% 0.22/0.40  fof(f8,plain,(
% 0.22/0.40    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0)),
% 0.22/0.40    inference(cnf_transformation,[],[f7])).
% 0.22/0.40  fof(f7,plain,(
% 0.22/0.40    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0)),
% 0.22/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).
% 0.22/0.40  fof(f6,plain,(
% 0.22/0.40    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0)),
% 0.22/0.40    introduced(choice_axiom,[])).
% 0.22/0.40  fof(f5,plain,(
% 0.22/0.40    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0)),
% 0.22/0.40    inference(ennf_transformation,[],[f4])).
% 0.22/0.40  fof(f4,negated_conjecture,(
% 0.22/0.40    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)),
% 0.22/0.40    inference(negated_conjecture,[],[f3])).
% 0.22/0.40  fof(f3,conjecture,(
% 0.22/0.40    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)),
% 0.22/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_enumset1)).
% 0.22/0.40  % SZS output end Proof for theBenchmark
% 0.22/0.40  % (22363)------------------------------
% 0.22/0.40  % (22363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.40  % (22363)Termination reason: Refutation
% 0.22/0.40  
% 0.22/0.40  % (22363)Memory used [KB]: 10490
% 0.22/0.40  % (22363)Time elapsed: 0.003 s
% 0.22/0.40  % (22363)------------------------------
% 0.22/0.40  % (22363)------------------------------
% 0.22/0.40  % (22351)Success in time 0.046 s
%------------------------------------------------------------------------------
