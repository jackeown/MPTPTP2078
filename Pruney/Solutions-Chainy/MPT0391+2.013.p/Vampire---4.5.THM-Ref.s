%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:50 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   28 (  37 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  72 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(subsumption_resolution,[],[f54,f22])).

fof(f22,plain,(
    k1_xboole_0 != k3_xboole_0(k1_setfam_1(sK1),sK2) ),
    inference(resolution,[],[f18,f14])).

fof(f14,plain,(
    ~ r1_xboole_0(k1_setfam_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
      & r1_xboole_0(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
      & r1_xboole_0(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r2_hidden(X0,X1) )
       => r1_xboole_0(k1_setfam_1(X1),X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_xboole_0(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_setfam_1)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f54,plain,(
    k1_xboole_0 = k3_xboole_0(k1_setfam_1(sK1),sK2) ),
    inference(forward_demodulation,[],[f51,f15])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f51,plain,(
    k3_xboole_0(k1_setfam_1(sK1),sK2) = k3_xboole_0(k1_setfam_1(sK1),k1_xboole_0) ),
    inference(superposition,[],[f50,f23])).

fof(f23,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f19,f13])).

fof(f13,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(k1_setfam_1(sK1),k3_xboole_0(sK0,X0)) = k3_xboole_0(k1_setfam_1(sK1),X0) ),
    inference(superposition,[],[f20,f49])).

fof(f49,plain,(
    k1_setfam_1(sK1) = k3_xboole_0(k1_setfam_1(sK1),sK0) ),
    inference(resolution,[],[f21,f12])).

fof(f12,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k1_setfam_1(X0) = k3_xboole_0(k1_setfam_1(X0),X1) ) ),
    inference(resolution,[],[f17,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:14 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.41  % (30997)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.19/0.41  % (30990)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.19/0.41  % (30990)Refutation found. Thanks to Tanya!
% 0.19/0.41  % SZS status Theorem for theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f55,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(subsumption_resolution,[],[f54,f22])).
% 0.19/0.41  fof(f22,plain,(
% 0.19/0.41    k1_xboole_0 != k3_xboole_0(k1_setfam_1(sK1),sK2)),
% 0.19/0.41    inference(resolution,[],[f18,f14])).
% 0.19/0.41  fof(f14,plain,(
% 0.19/0.41    ~r1_xboole_0(k1_setfam_1(sK1),sK2)),
% 0.19/0.41    inference(cnf_transformation,[],[f9])).
% 0.19/0.41  fof(f9,plain,(
% 0.19/0.41    ? [X0,X1,X2] : (~r1_xboole_0(k1_setfam_1(X1),X2) & r1_xboole_0(X0,X2) & r2_hidden(X0,X1))),
% 0.19/0.41    inference(flattening,[],[f8])).
% 0.19/0.41  fof(f8,plain,(
% 0.19/0.41    ? [X0,X1,X2] : (~r1_xboole_0(k1_setfam_1(X1),X2) & (r1_xboole_0(X0,X2) & r2_hidden(X0,X1)))),
% 0.19/0.41    inference(ennf_transformation,[],[f7])).
% 0.19/0.41  fof(f7,negated_conjecture,(
% 0.19/0.41    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r2_hidden(X0,X1)) => r1_xboole_0(k1_setfam_1(X1),X2))),
% 0.19/0.41    inference(negated_conjecture,[],[f6])).
% 0.19/0.41  fof(f6,conjecture,(
% 0.19/0.41    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r2_hidden(X0,X1)) => r1_xboole_0(k1_setfam_1(X1),X2))),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_setfam_1)).
% 0.19/0.41  fof(f18,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.19/0.41    inference(cnf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.19/0.41  fof(f54,plain,(
% 0.19/0.41    k1_xboole_0 = k3_xboole_0(k1_setfam_1(sK1),sK2)),
% 0.19/0.41    inference(forward_demodulation,[],[f51,f15])).
% 0.19/0.41  fof(f15,plain,(
% 0.19/0.41    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f4])).
% 0.19/0.41  fof(f4,axiom,(
% 0.19/0.41    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.19/0.41  fof(f51,plain,(
% 0.19/0.41    k3_xboole_0(k1_setfam_1(sK1),sK2) = k3_xboole_0(k1_setfam_1(sK1),k1_xboole_0)),
% 0.19/0.41    inference(superposition,[],[f50,f23])).
% 0.19/0.41  fof(f23,plain,(
% 0.19/0.41    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.19/0.41    inference(resolution,[],[f19,f13])).
% 0.19/0.41  fof(f13,plain,(
% 0.19/0.41    r1_xboole_0(sK0,sK2)),
% 0.19/0.41    inference(cnf_transformation,[],[f9])).
% 0.19/0.41  fof(f19,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.19/0.41    inference(cnf_transformation,[],[f1])).
% 0.19/0.41  fof(f50,plain,(
% 0.19/0.41    ( ! [X0] : (k3_xboole_0(k1_setfam_1(sK1),k3_xboole_0(sK0,X0)) = k3_xboole_0(k1_setfam_1(sK1),X0)) )),
% 0.19/0.41    inference(superposition,[],[f20,f49])).
% 0.19/0.41  fof(f49,plain,(
% 0.19/0.41    k1_setfam_1(sK1) = k3_xboole_0(k1_setfam_1(sK1),sK0)),
% 0.19/0.41    inference(resolution,[],[f21,f12])).
% 0.19/0.41  fof(f12,plain,(
% 0.19/0.41    r2_hidden(sK0,sK1)),
% 0.19/0.41    inference(cnf_transformation,[],[f9])).
% 0.19/0.41  fof(f21,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k1_setfam_1(X0) = k3_xboole_0(k1_setfam_1(X0),X1)) )),
% 0.19/0.41    inference(resolution,[],[f17,f16])).
% 0.19/0.41  fof(f16,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f10])).
% 0.19/0.41  fof(f10,plain,(
% 0.19/0.41    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.19/0.41    inference(ennf_transformation,[],[f5])).
% 0.19/0.41  fof(f5,axiom,(
% 0.19/0.41    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.19/0.41  fof(f17,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.19/0.41    inference(cnf_transformation,[],[f11])).
% 0.19/0.41  fof(f11,plain,(
% 0.19/0.41    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.41    inference(ennf_transformation,[],[f3])).
% 0.19/0.41  fof(f3,axiom,(
% 0.19/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.41  fof(f20,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f2])).
% 0.19/0.41  fof(f2,axiom,(
% 0.19/0.41    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.19/0.41  % SZS output end Proof for theBenchmark
% 0.19/0.41  % (30990)------------------------------
% 0.19/0.41  % (30990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (30990)Termination reason: Refutation
% 0.19/0.41  
% 0.19/0.41  % (30990)Memory used [KB]: 10490
% 0.19/0.41  % (30990)Time elapsed: 0.006 s
% 0.19/0.41  % (30990)------------------------------
% 0.19/0.41  % (30990)------------------------------
% 0.19/0.42  % (30989)Success in time 0.062 s
%------------------------------------------------------------------------------
