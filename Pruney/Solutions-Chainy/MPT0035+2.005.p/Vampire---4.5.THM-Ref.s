%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   20 (  23 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  32 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(subsumption_resolution,[],[f25,f11])).

fof(f11,plain,(
    sK0 != k3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(X0,X1) != X0
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => k3_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f25,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f22,f17])).

fof(f17,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f14,f10])).

fof(f10,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f14,plain,(
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

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f18,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f15,f12])).

fof(f12,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f15,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.41  % (1908)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.41  % (1906)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.41  % (1901)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.41  % (1901)Refutation found. Thanks to Tanya!
% 0.22/0.41  % SZS status Theorem for theBenchmark
% 0.22/0.41  % SZS output start Proof for theBenchmark
% 0.22/0.41  fof(f30,plain,(
% 0.22/0.41    $false),
% 0.22/0.41    inference(subsumption_resolution,[],[f25,f11])).
% 0.22/0.41  fof(f11,plain,(
% 0.22/0.41    sK0 != k3_xboole_0(sK0,sK1)),
% 0.22/0.41    inference(cnf_transformation,[],[f8])).
% 0.22/0.41  fof(f8,plain,(
% 0.22/0.41    ? [X0,X1] : (k3_xboole_0(X0,X1) != X0 & r1_tarski(X0,X1))),
% 0.22/0.41    inference(ennf_transformation,[],[f6])).
% 0.22/0.41  fof(f6,negated_conjecture,(
% 0.22/0.41    ~! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.41    inference(negated_conjecture,[],[f5])).
% 0.22/0.41  fof(f5,conjecture,(
% 0.22/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.41  fof(f25,plain,(
% 0.22/0.41    sK0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.41    inference(superposition,[],[f22,f17])).
% 0.22/0.41  fof(f17,plain,(
% 0.22/0.41    sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.41    inference(resolution,[],[f14,f10])).
% 0.22/0.41  fof(f10,plain,(
% 0.22/0.41    r1_tarski(sK0,sK1)),
% 0.22/0.41    inference(cnf_transformation,[],[f8])).
% 0.22/0.41  fof(f14,plain,(
% 0.22/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.41    inference(cnf_transformation,[],[f9])).
% 0.22/0.41  fof(f9,plain,(
% 0.22/0.41    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.41    inference(ennf_transformation,[],[f2])).
% 0.22/0.41  fof(f2,axiom,(
% 0.22/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.41  fof(f22,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.22/0.41    inference(forward_demodulation,[],[f18,f13])).
% 0.22/0.41  fof(f13,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.22/0.41    inference(cnf_transformation,[],[f3])).
% 0.22/0.41  fof(f3,axiom,(
% 0.22/0.41    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.22/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.22/0.41  fof(f18,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.41    inference(superposition,[],[f15,f12])).
% 0.22/0.41  fof(f12,plain,(
% 0.22/0.41    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.41    inference(cnf_transformation,[],[f7])).
% 0.22/0.41  fof(f7,plain,(
% 0.22/0.41    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.41    inference(rectify,[],[f1])).
% 0.22/0.41  fof(f1,axiom,(
% 0.22/0.41    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.41  fof(f15,plain,(
% 0.22/0.41    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.41    inference(cnf_transformation,[],[f4])).
% 0.22/0.41  fof(f4,axiom,(
% 0.22/0.41    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.22/0.41  % SZS output end Proof for theBenchmark
% 0.22/0.41  % (1901)------------------------------
% 0.22/0.41  % (1901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.41  % (1901)Termination reason: Refutation
% 0.22/0.41  
% 0.22/0.41  % (1901)Memory used [KB]: 10490
% 0.22/0.41  % (1901)Time elapsed: 0.004 s
% 0.22/0.41  % (1901)------------------------------
% 0.22/0.41  % (1901)------------------------------
% 0.22/0.42  % (1900)Success in time 0.061 s
%------------------------------------------------------------------------------
