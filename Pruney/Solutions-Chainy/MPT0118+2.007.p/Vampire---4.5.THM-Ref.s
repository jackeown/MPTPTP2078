%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   20 (  28 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :   10
%              Number of atoms          :   21 (  29 expanded)
%              Number of equality atoms :   20 (  28 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f86])).

fof(f86,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f85,f13])).

fof(f13,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f85,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f74,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f74,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f16,f62])).

fof(f62,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5)) ),
    inference(superposition,[],[f25,f14])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f14,f11])).

fof(f11,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f16,plain,(
    k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f15,f11])).

fof(f15,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f10,f11])).

fof(f10,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1)
   => k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:26:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (11580)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (11586)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (11593)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (11588)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (11585)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (11590)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (11579)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (11582)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (11578)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (11581)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (11581)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f86])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.49    inference(forward_demodulation,[],[f85,f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.49    inference(superposition,[],[f74,f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.49    inference(backward_demodulation,[],[f16,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5))) )),
% 0.22/0.49    inference(superposition,[],[f25,f14])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)) )),
% 0.22/0.49    inference(superposition,[],[f14,f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))),
% 0.22/0.49    inference(forward_demodulation,[],[f15,f11])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.49    inference(backward_demodulation,[],[f10,f11])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1) => k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 0.22/0.49    inference(negated_conjecture,[],[f5])).
% 0.22/0.49  fof(f5,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (11581)------------------------------
% 0.22/0.49  % (11581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (11581)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (11581)Memory used [KB]: 1663
% 0.22/0.49  % (11581)Time elapsed: 0.075 s
% 0.22/0.49  % (11581)------------------------------
% 0.22/0.49  % (11581)------------------------------
% 0.22/0.49  % (11577)Success in time 0.126 s
%------------------------------------------------------------------------------
