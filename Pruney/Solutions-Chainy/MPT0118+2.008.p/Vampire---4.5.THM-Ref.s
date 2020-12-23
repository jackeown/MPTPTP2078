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
% DateTime   : Thu Dec  3 12:32:55 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   13 (  17 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    7
%              Number of atoms          :   13 (  17 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f21])).

fof(f21,plain,(
    k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f11,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2)) ),
    inference(superposition,[],[f8,f7])).

fof(f7,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f8,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f11,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f9,f7])).

fof(f9,plain,(
    k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f6,f7])).

fof(f6,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:08:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.41  % (24744)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.19/0.41  % (24736)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.19/0.41  % (24742)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.41  % (24736)Refutation found. Thanks to Tanya!
% 0.19/0.41  % SZS status Theorem for theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f22,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(trivial_inequality_removal,[],[f21])).
% 0.19/0.41  fof(f21,plain,(
% 0.19/0.41    k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.19/0.41    inference(superposition,[],[f11,f13])).
% 0.19/0.41  fof(f13,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))) )),
% 0.19/0.41    inference(superposition,[],[f8,f7])).
% 0.19/0.41  fof(f7,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.41  fof(f8,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f2])).
% 0.19/0.41  fof(f2,axiom,(
% 0.19/0.41    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).
% 0.19/0.41  fof(f11,plain,(
% 0.19/0.41    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.19/0.41    inference(forward_demodulation,[],[f9,f7])).
% 0.19/0.41  fof(f9,plain,(
% 0.19/0.41    k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))),
% 0.19/0.41    inference(superposition,[],[f6,f7])).
% 0.19/0.41  fof(f6,plain,(
% 0.19/0.41    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.19/0.41    inference(cnf_transformation,[],[f5])).
% 0.19/0.41  fof(f5,plain,(
% 0.19/0.41    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 0.19/0.41    inference(ennf_transformation,[],[f4])).
% 0.19/0.41  fof(f4,negated_conjecture,(
% 0.19/0.41    ~! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 0.19/0.41    inference(negated_conjecture,[],[f3])).
% 0.19/0.41  fof(f3,conjecture,(
% 0.19/0.41    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).
% 0.19/0.41  % SZS output end Proof for theBenchmark
% 0.19/0.41  % (24736)------------------------------
% 0.19/0.41  % (24736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (24736)Termination reason: Refutation
% 0.19/0.41  
% 0.19/0.41  % (24736)Memory used [KB]: 10490
% 0.19/0.41  % (24736)Time elapsed: 0.005 s
% 0.19/0.41  % (24736)------------------------------
% 0.19/0.41  % (24736)------------------------------
% 0.19/0.41  % (24735)Success in time 0.062 s
%------------------------------------------------------------------------------
