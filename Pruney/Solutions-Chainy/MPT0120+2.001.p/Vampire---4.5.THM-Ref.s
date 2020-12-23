%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   12 (  16 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    8
%              Number of atoms          :   13 (  17 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f16])).

fof(f16,plain,(
    k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))) != k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(forward_demodulation,[],[f15,f8])).

fof(f8,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f15,plain,(
    k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) != k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(forward_demodulation,[],[f11,f8])).

fof(f11,plain,(
    k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) != k2_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f7,f8])).

fof(f7,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f4,f5])).

fof(f5,plain,
    ( ? [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) != k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))
   => k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) != k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:06:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (21331)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.42  % (21332)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (21331)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(trivial_inequality_removal,[],[f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3))) != k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)))),
% 0.22/0.42    inference(forward_demodulation,[],[f15,f8])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) != k2_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3)))),
% 0.22/0.42    inference(forward_demodulation,[],[f11,f8])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) != k2_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3))),
% 0.22/0.42    inference(superposition,[],[f7,f8])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3))),
% 0.22/0.42    inference(cnf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,plain,(
% 0.22/0.42    k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3))),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f4,f5])).
% 0.22/0.42  fof(f5,plain,(
% 0.22/0.42    ? [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) != k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) => k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f4,plain,(
% 0.22/0.42    ? [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) != k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))),
% 0.22/0.42    inference(negated_conjecture,[],[f2])).
% 0.22/0.42  fof(f2,conjecture,(
% 0.22/0.42    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_xboole_1)).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (21331)------------------------------
% 0.22/0.42  % (21331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (21331)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (21331)Memory used [KB]: 6012
% 0.22/0.42  % (21331)Time elapsed: 0.003 s
% 0.22/0.42  % (21331)------------------------------
% 0.22/0.42  % (21331)------------------------------
% 0.22/0.43  % (21326)Success in time 0.065 s
%------------------------------------------------------------------------------
