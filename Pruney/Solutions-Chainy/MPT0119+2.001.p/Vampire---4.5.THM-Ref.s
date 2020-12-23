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
% DateTime   : Thu Dec  3 12:32:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   22 (  30 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :   12
%              Number of atoms          :   23 (  31 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f39])).

fof(f39,plain,(
    k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) != k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) ),
    inference(superposition,[],[f32,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f32,plain,(
    k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) != k2_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)),k3_xboole_0(sK1,k4_xboole_0(sK2,sK0))) ),
    inference(forward_demodulation,[],[f31,f11])).

fof(f11,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f31,plain,(
    k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) != k2_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK1,k4_xboole_0(sK2,sK0))) ),
    inference(forward_demodulation,[],[f30,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).

fof(f30,plain,(
    k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) != k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK2,sK0))) ),
    inference(forward_demodulation,[],[f29,f11])).

fof(f29,plain,(
    k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) != k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k4_xboole_0(sK2,sK0),sK1)) ),
    inference(forward_demodulation,[],[f28,f14])).

fof(f28,plain,(
    k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k4_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(sK0,sK1))) != k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) ),
    inference(forward_demodulation,[],[f15,f11])).

fof(f15,plain,(
    k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k4_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(sK0,sK1))) != k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0)),sK1) ),
    inference(definition_unfolding,[],[f10,f12,f12])).

fof(f12,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f10,plain,(
    k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k5_xboole_0(X0,X2),X1)
   => k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:58:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (29512)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (29507)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (29508)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (29518)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (29508)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) != k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0)))),
% 0.22/0.48    inference(superposition,[],[f32,f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) != k2_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)),k3_xboole_0(sK1,k4_xboole_0(sK2,sK0)))),
% 0.22/0.48    inference(forward_demodulation,[],[f31,f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) != k2_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK2),sK1),k3_xboole_0(sK1,k4_xboole_0(sK2,sK0)))),
% 0.22/0.48    inference(forward_demodulation,[],[f30,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) != k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(sK1,k4_xboole_0(sK2,sK0)))),
% 0.22/0.48    inference(forward_demodulation,[],[f29,f11])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0))) != k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k3_xboole_0(k4_xboole_0(sK2,sK0),sK1))),
% 0.22/0.48    inference(forward_demodulation,[],[f28,f14])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k4_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(sK0,sK1))) != k3_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0)))),
% 0.22/0.48    inference(forward_demodulation,[],[f15,f11])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    k2_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)),k4_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(sK0,sK1))) != k3_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK2,sK0)),sK1)),
% 0.22/0.48    inference(definition_unfolding,[],[f10,f12,f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k5_xboole_0(X0,X2),X1) => k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 0.22/0.48    inference(negated_conjecture,[],[f5])).
% 0.22/0.48  fof(f5,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (29508)------------------------------
% 0.22/0.48  % (29508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (29508)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (29508)Memory used [KB]: 6140
% 0.22/0.48  % (29508)Time elapsed: 0.052 s
% 0.22/0.48  % (29508)------------------------------
% 0.22/0.48  % (29508)------------------------------
% 0.22/0.48  % (29509)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (29501)Success in time 0.113 s
%------------------------------------------------------------------------------
