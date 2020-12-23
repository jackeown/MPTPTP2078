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
% DateTime   : Thu Dec  3 12:29:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   24 (  31 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  40 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f502,plain,(
    $false ),
    inference(subsumption_resolution,[],[f482,f11])).

fof(f11,plain,(
    ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
       => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f482,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f178,f231])).

fof(f231,plain,(
    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f45,f19])).

fof(f19,plain,(
    sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(resolution,[],[f15,f10])).

fof(f10,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f45,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X6,k2_xboole_0(k4_xboole_0(X7,X6),X8)) = k2_xboole_0(X6,k2_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f34,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f34,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X6,k2_xboole_0(k4_xboole_0(X7,X6),X8)) = k2_xboole_0(k2_xboole_0(X6,X7),X8) ),
    inference(superposition,[],[f16,f14])).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f178,plain,(
    ! [X6,X7,X5] : r1_tarski(X5,k2_xboole_0(X7,k2_xboole_0(X5,X6))) ),
    inference(superposition,[],[f12,f37])).

fof(f37,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f16,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f12,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:33:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.42  % (25146)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  % (25143)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (25145)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.44  % (25147)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (25142)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.44  % (25148)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (25149)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.45  % (25145)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f502,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(subsumption_resolution,[],[f482,f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.45    inference(cnf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ? [X0,X1,X2] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) & r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.45    inference(negated_conjecture,[],[f6])).
% 0.22/0.45  fof(f6,conjecture,(
% 0.22/0.45    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.22/0.45  fof(f482,plain,(
% 0.22/0.45    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.45    inference(superposition,[],[f178,f231])).
% 0.22/0.45  fof(f231,plain,(
% 0.22/0.45    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.22/0.45    inference(superposition,[],[f45,f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 0.22/0.45    inference(resolution,[],[f15,f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.22/0.45    inference(cnf_transformation,[],[f8])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.45    inference(cnf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.45  fof(f45,plain,(
% 0.22/0.45    ( ! [X6,X8,X7] : (k2_xboole_0(X6,k2_xboole_0(k4_xboole_0(X7,X6),X8)) = k2_xboole_0(X6,k2_xboole_0(X7,X8))) )),
% 0.22/0.45    inference(forward_demodulation,[],[f34,f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ( ! [X6,X8,X7] : (k2_xboole_0(X6,k2_xboole_0(k4_xboole_0(X7,X6),X8)) = k2_xboole_0(k2_xboole_0(X6,X7),X8)) )),
% 0.22/0.45    inference(superposition,[],[f16,f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.45  fof(f178,plain,(
% 0.22/0.45    ( ! [X6,X7,X5] : (r1_tarski(X5,k2_xboole_0(X7,k2_xboole_0(X5,X6)))) )),
% 0.22/0.45    inference(superposition,[],[f12,f37])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4))) )),
% 0.22/0.45    inference(superposition,[],[f16,f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (25145)------------------------------
% 0.22/0.45  % (25145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (25145)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (25145)Memory used [KB]: 11257
% 0.22/0.45  % (25145)Time elapsed: 0.026 s
% 0.22/0.45  % (25145)------------------------------
% 0.22/0.45  % (25145)------------------------------
% 0.22/0.45  % (25141)Success in time 0.093 s
%------------------------------------------------------------------------------
