%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   25 (  45 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   26 (  46 expanded)
%              Number of equality atoms :   25 (  45 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(subsumption_resolution,[],[f233,f222])).

fof(f222,plain,(
    ! [X10,X8,X9] : k3_xboole_0(X8,k4_xboole_0(X9,X10)) = k3_xboole_0(X9,k4_xboole_0(X8,k3_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f221,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f221,plain,(
    ! [X10,X8,X9] : k4_xboole_0(k3_xboole_0(X8,X9),X10) = k3_xboole_0(X9,k4_xboole_0(X8,k3_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f220,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f220,plain,(
    ! [X10,X8,X9] : k4_xboole_0(k3_xboole_0(X8,X9),X10) = k3_xboole_0(X9,k4_xboole_0(X8,k3_xboole_0(X8,k3_xboole_0(X9,X10)))) ),
    inference(forward_demodulation,[],[f205,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f205,plain,(
    ! [X10,X8,X9] : k4_xboole_0(k3_xboole_0(X8,X9),X10) = k3_xboole_0(X9,k4_xboole_0(X8,k3_xboole_0(k3_xboole_0(X8,X9),X10))) ),
    inference(superposition,[],[f116,f20])).

fof(f116,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f23,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f233,plain,(
    k3_xboole_0(sK1,k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f218,f116])).

fof(f218,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f27,f203])).

fof(f203,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5)) ),
    inference(superposition,[],[f116,f23])).

fof(f27,plain,(
    k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f26,f19])).

fof(f26,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f16,f19])).

fof(f16,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1)
   => k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:24:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (24059)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (24060)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (24056)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.44  % (24062)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.45  % (24056)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f235,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(subsumption_resolution,[],[f233,f222])).
% 0.22/0.45  fof(f222,plain,(
% 0.22/0.45    ( ! [X10,X8,X9] : (k3_xboole_0(X8,k4_xboole_0(X9,X10)) = k3_xboole_0(X9,k4_xboole_0(X8,k3_xboole_0(X9,X10)))) )),
% 0.22/0.45    inference(forward_demodulation,[],[f221,f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f6])).
% 0.22/0.45  fof(f6,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.45  fof(f221,plain,(
% 0.22/0.45    ( ! [X10,X8,X9] : (k4_xboole_0(k3_xboole_0(X8,X9),X10) = k3_xboole_0(X9,k4_xboole_0(X8,k3_xboole_0(X9,X10)))) )),
% 0.22/0.45    inference(forward_demodulation,[],[f220,f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.45  fof(f220,plain,(
% 0.22/0.45    ( ! [X10,X8,X9] : (k4_xboole_0(k3_xboole_0(X8,X9),X10) = k3_xboole_0(X9,k4_xboole_0(X8,k3_xboole_0(X8,k3_xboole_0(X9,X10))))) )),
% 0.22/0.45    inference(forward_demodulation,[],[f205,f24])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.22/0.45  fof(f205,plain,(
% 0.22/0.45    ( ! [X10,X8,X9] : (k4_xboole_0(k3_xboole_0(X8,X9),X10) = k3_xboole_0(X9,k4_xboole_0(X8,k3_xboole_0(k3_xboole_0(X8,X9),X10)))) )),
% 0.22/0.45    inference(superposition,[],[f116,f20])).
% 0.22/0.45  fof(f116,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)) )),
% 0.22/0.45    inference(superposition,[],[f23,f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.45  fof(f233,plain,(
% 0.22/0.45    k3_xboole_0(sK1,k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.45    inference(superposition,[],[f218,f116])).
% 0.22/0.45  fof(f218,plain,(
% 0.22/0.45    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.45    inference(backward_demodulation,[],[f27,f203])).
% 0.22/0.45  fof(f203,plain,(
% 0.22/0.45    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5))) )),
% 0.22/0.45    inference(superposition,[],[f116,f23])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))),
% 0.22/0.45    inference(forward_demodulation,[],[f26,f19])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.45    inference(backward_demodulation,[],[f16,f19])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1) => k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) != k3_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) != k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 0.22/0.45    inference(ennf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 0.22/0.45    inference(negated_conjecture,[],[f10])).
% 0.22/0.45  fof(f10,conjecture,(
% 0.22/0.45    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_xboole_1)).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (24056)------------------------------
% 0.22/0.45  % (24056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (24056)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (24056)Memory used [KB]: 6268
% 0.22/0.45  % (24056)Time elapsed: 0.035 s
% 0.22/0.45  % (24056)------------------------------
% 0.22/0.45  % (24056)------------------------------
% 0.22/0.45  % (24050)Success in time 0.087 s
%------------------------------------------------------------------------------
