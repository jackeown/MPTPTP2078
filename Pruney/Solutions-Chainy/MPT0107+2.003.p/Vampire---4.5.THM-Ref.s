%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :   28 (  30 expanded)
%              Number of equality atoms :   27 (  29 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
% (23798)Time elapsed: 0.079 s
% (23798)------------------------------
% (23798)------------------------------
fof(f98,plain,(
    $false ),
    inference(subsumption_resolution,[],[f97,f55])).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f97,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f96,f63])).

fof(f63,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

% (23787)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f96,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f95,f65])).

% (23792)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f95,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))) ),
    inference(backward_demodulation,[],[f94,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f94,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) ),
    inference(backward_demodulation,[],[f86,f88])).

fof(f88,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f68,f66])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f86,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) ),
    inference(definition_unfolding,[],[f52,f70,f66])).

fof(f70,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f52,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f49])).

fof(f49,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:59:57 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.52  % (23793)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (23797)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (23804)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (23804)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (23813)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (23805)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (23798)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (23785)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (23807)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (23786)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (23798)Refutation not found, incomplete strategy% (23798)------------------------------
% 0.22/0.54  % (23798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23785)Refutation not found, incomplete strategy% (23785)------------------------------
% 0.22/0.54  % (23785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23785)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23785)Memory used [KB]: 1791
% 0.22/0.54  % (23785)Time elapsed: 0.123 s
% 0.22/0.54  % (23785)------------------------------
% 0.22/0.54  % (23785)------------------------------
% 0.22/0.54  % (23798)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23798)Memory used [KB]: 1663
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  % (23798)Time elapsed: 0.079 s
% 0.22/0.54  % (23798)------------------------------
% 0.22/0.54  % (23798)------------------------------
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f97,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.22/0.54    inference(forward_demodulation,[],[f96,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.22/0.54  % (23787)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 0.22/0.54    inference(forward_demodulation,[],[f95,f65])).
% 0.22/0.54  % (23792)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)))),
% 0.22/0.54    inference(backward_demodulation,[],[f94,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),
% 0.22/0.54    inference(backward_demodulation,[],[f86,f88])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f68,f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,axiom,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),
% 0.22/0.54    inference(definition_unfolding,[],[f52,f70,f66])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    inference(negated_conjecture,[],[f32])).
% 0.22/0.54  fof(f32,conjecture,(
% 0.22/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (23804)------------------------------
% 0.22/0.54  % (23804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23804)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (23804)Memory used [KB]: 10618
% 0.22/0.54  % (23804)Time elapsed: 0.007 s
% 0.22/0.54  % (23804)------------------------------
% 0.22/0.54  % (23804)------------------------------
% 0.22/0.55  % (23783)Success in time 0.18 s
%------------------------------------------------------------------------------
