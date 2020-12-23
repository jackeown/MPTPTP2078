%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:29 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   10 (  10 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    5
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,plain,(
    $false ),
    inference(subsumption_resolution,[],[f11,f8])).

fof(f8,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).

fof(f11,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0) ),
    inference(superposition,[],[f6,f7])).

fof(f7,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).

fof(f6,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:42:07 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.42  % (30251)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.14/0.43  % (30253)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.14/0.43  % (30251)Refutation found. Thanks to Tanya!
% 0.14/0.43  % SZS status Theorem for theBenchmark
% 0.14/0.43  % SZS output start Proof for theBenchmark
% 0.14/0.43  fof(f12,plain,(
% 0.14/0.43    $false),
% 0.14/0.43    inference(subsumption_resolution,[],[f11,f8])).
% 0.14/0.43  fof(f8,plain,(
% 0.14/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)) )),
% 0.14/0.43    inference(cnf_transformation,[],[f2])).
% 0.14/0.43  fof(f2,axiom,(
% 0.14/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X2,X0)),
% 0.14/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_enumset1)).
% 0.14/0.43  fof(f11,plain,(
% 0.14/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK2,sK0)),
% 0.14/0.43    inference(superposition,[],[f6,f7])).
% 0.14/0.43  fof(f7,plain,(
% 0.14/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 0.14/0.43    inference(cnf_transformation,[],[f1])).
% 0.14/0.43  fof(f1,axiom,(
% 0.14/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.14/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l123_enumset1)).
% 0.14/0.43  fof(f6,plain,(
% 0.14/0.43    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK1,sK3,sK0)),
% 0.14/0.43    inference(cnf_transformation,[],[f5])).
% 0.14/0.43  fof(f5,plain,(
% 0.14/0.43    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X1,X3,X0)),
% 0.14/0.43    inference(ennf_transformation,[],[f4])).
% 0.14/0.43  fof(f4,negated_conjecture,(
% 0.14/0.43    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)),
% 0.14/0.43    inference(negated_conjecture,[],[f3])).
% 0.14/0.43  fof(f3,conjecture,(
% 0.14/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X3,X0)),
% 0.14/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_enumset1)).
% 0.14/0.43  % SZS output end Proof for theBenchmark
% 0.14/0.43  % (30251)------------------------------
% 0.14/0.43  % (30251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.43  % (30251)Termination reason: Refutation
% 0.14/0.43  
% 0.14/0.43  % (30251)Memory used [KB]: 10490
% 0.14/0.43  % (30251)Time elapsed: 0.004 s
% 0.14/0.43  % (30251)------------------------------
% 0.14/0.43  % (30251)------------------------------
% 0.14/0.43  % (30250)Success in time 0.06 s
%------------------------------------------------------------------------------
