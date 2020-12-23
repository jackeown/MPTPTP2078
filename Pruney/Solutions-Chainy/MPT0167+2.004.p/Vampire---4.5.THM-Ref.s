%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
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
    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(definition_unfolding,[],[f8,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f9,f10])).

fof(f10,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).

fof(f9,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f8,plain,(
    k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_enumset1(X0,X0,X0,X0,X1)
   => k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (7198)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.43  % (7198)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(trivial_inequality_removal,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 0.20/0.43    inference(definition_unfolding,[],[f8,f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f9,f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).
% 0.20/0.43  fof(f6,plain,(
% 0.20/0.43    ? [X0,X1] : k2_tarski(X0,X1) != k3_enumset1(X0,X0,X0,X0,X1) => k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f5,plain,(
% 0.20/0.43    ? [X0,X1] : k2_tarski(X0,X1) != k3_enumset1(X0,X0,X0,X0,X1)),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)),
% 0.20/0.43    inference(negated_conjecture,[],[f3])).
% 0.20/0.43  fof(f3,conjecture,(
% 0.20/0.43    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_enumset1)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (7198)------------------------------
% 0.20/0.43  % (7198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (7198)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (7198)Memory used [KB]: 10490
% 0.20/0.43  % (7198)Time elapsed: 0.003 s
% 0.20/0.43  % (7198)------------------------------
% 0.20/0.43  % (7198)------------------------------
% 0.20/0.43  % (7182)Success in time 0.073 s
%------------------------------------------------------------------------------
