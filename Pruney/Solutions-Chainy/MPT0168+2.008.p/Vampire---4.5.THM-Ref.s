%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:55 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f12])).

fof(f12,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(definition_unfolding,[],[f8,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f9,f10])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).

fof(f9,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f8,plain,(
    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:19:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.42  % (18148)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.14/0.42  % (18148)Refutation found. Thanks to Tanya!
% 0.14/0.42  % SZS status Theorem for theBenchmark
% 0.14/0.42  % SZS output start Proof for theBenchmark
% 0.14/0.42  fof(f13,plain,(
% 0.14/0.42    $false),
% 0.14/0.42    inference(trivial_inequality_removal,[],[f12])).
% 0.14/0.42  fof(f12,plain,(
% 0.14/0.42    k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.14/0.42    inference(definition_unfolding,[],[f8,f11])).
% 0.14/0.42  fof(f11,plain,(
% 0.14/0.42    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.14/0.42    inference(definition_unfolding,[],[f9,f10])).
% 0.14/0.42  fof(f10,plain,(
% 0.14/0.42    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f2])).
% 0.14/0.42  fof(f2,axiom,(
% 0.14/0.42    ! [X0,X1,X2,X3] : k4_enumset1(X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_enumset1)).
% 0.14/0.42  fof(f9,plain,(
% 0.14/0.42    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f1])).
% 0.14/0.42  fof(f1,axiom,(
% 0.14/0.42    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.14/0.42  fof(f8,plain,(
% 0.14/0.42    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.14/0.42    inference(cnf_transformation,[],[f7])).
% 0.14/0.42  fof(f7,plain,(
% 0.14/0.42    k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.14/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).
% 0.14/0.42  fof(f6,plain,(
% 0.14/0.42    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k4_enumset1(sK0,sK0,sK0,sK0,sK1,sK2)),
% 0.14/0.42    introduced(choice_axiom,[])).
% 0.14/0.42  fof(f5,plain,(
% 0.14/0.42    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 0.14/0.42    inference(ennf_transformation,[],[f4])).
% 0.14/0.42  fof(f4,negated_conjecture,(
% 0.14/0.42    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 0.14/0.42    inference(negated_conjecture,[],[f3])).
% 0.14/0.42  fof(f3,conjecture,(
% 0.14/0.42    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_enumset1)).
% 0.14/0.42  % SZS output end Proof for theBenchmark
% 0.14/0.42  % (18148)------------------------------
% 0.14/0.42  % (18148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.42  % (18148)Termination reason: Refutation
% 0.14/0.42  
% 0.14/0.42  % (18148)Memory used [KB]: 1535
% 0.14/0.42  % (18148)Time elapsed: 0.003 s
% 0.14/0.42  % (18148)------------------------------
% 0.14/0.42  % (18148)------------------------------
% 0.14/0.42  % (18135)Success in time 0.06 s
%------------------------------------------------------------------------------
