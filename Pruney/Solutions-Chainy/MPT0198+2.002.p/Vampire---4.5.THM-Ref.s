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
% DateTime   : Thu Dec  3 12:34:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
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
fof(f22,plain,(
    $false ),
    inference(subsumption_resolution,[],[f16,f7])).

fof(f7,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).

fof(f16,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK0,sK1,sK3) ),
    inference(superposition,[],[f6,f8])).

fof(f8,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(f6,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X1,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:03:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.41  % (31540)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.41  % (31540)Refutation found. Thanks to Tanya!
% 0.22/0.41  % SZS status Theorem for theBenchmark
% 0.22/0.41  % SZS output start Proof for theBenchmark
% 0.22/0.41  fof(f22,plain,(
% 0.22/0.41    $false),
% 0.22/0.41    inference(subsumption_resolution,[],[f16,f7])).
% 0.22/0.41  fof(f7,plain,(
% 0.22/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f1])).
% 0.22/0.41  fof(f1,axiom,(
% 0.22/0.41    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X0,X3)),
% 0.22/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l123_enumset1)).
% 0.22/0.41  fof(f16,plain,(
% 0.22/0.41    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK0,sK1,sK3)),
% 0.22/0.41    inference(superposition,[],[f6,f8])).
% 0.22/0.41  fof(f8,plain,(
% 0.22/0.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f2])).
% 0.22/0.41  fof(f2,axiom,(
% 0.22/0.41    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 0.22/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).
% 0.22/0.41  fof(f6,plain,(
% 0.22/0.41    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK2,sK3,sK1,sK0)),
% 0.22/0.41    inference(cnf_transformation,[],[f5])).
% 0.22/0.41  fof(f5,plain,(
% 0.22/0.41    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X2,X3,X1,X0)),
% 0.22/0.41    inference(ennf_transformation,[],[f4])).
% 0.22/0.41  fof(f4,negated_conjecture,(
% 0.22/0.41    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)),
% 0.22/0.41    inference(negated_conjecture,[],[f3])).
% 0.22/0.41  fof(f3,conjecture,(
% 0.22/0.41    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X3,X1,X0)),
% 0.22/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_enumset1)).
% 0.22/0.41  % SZS output end Proof for theBenchmark
% 0.22/0.41  % (31540)------------------------------
% 0.22/0.41  % (31540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.41  % (31540)Termination reason: Refutation
% 0.22/0.41  
% 0.22/0.41  % (31540)Memory used [KB]: 10490
% 0.22/0.41  % (31540)Time elapsed: 0.002 s
% 0.22/0.41  % (31540)------------------------------
% 0.22/0.41  % (31540)------------------------------
% 0.22/0.41  % (31536)Success in time 0.047 s
%------------------------------------------------------------------------------
