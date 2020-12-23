%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  37 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  72 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(subsumption_resolution,[],[f65,f47])).

fof(f47,plain,(
    r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,(
    r2_hidden(sK2(sK0,sK1),sK0) ),
    inference(resolution,[],[f13,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f13,plain,(
    ~ r1_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_setfam_1(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).

fof(f40,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | r2_hidden(X4,sK1) ) ),
    inference(superposition,[],[f28,f30])).

fof(f30,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f12,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f12,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f65,plain,(
    ~ r2_hidden(sK2(sK0,sK1),sK1) ),
    inference(superposition,[],[f61,f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f61,plain,(
    ! [X0] : ~ r2_hidden(k2_xboole_0(sK2(sK0,sK1),X0),sK1) ),
    inference(resolution,[],[f31,f15])).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f31,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2(sK0,sK1),X0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f13,f17])).

fof(f17,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r1_tarski(sK2(X0,X1),X3)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:19:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (27083)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (27091)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (27091)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f65,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    r2_hidden(sK2(sK0,sK1),sK1)),
% 0.22/0.48    inference(resolution,[],[f40,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    r2_hidden(sK2(sK0,sK1),sK0)),
% 0.22/0.48    inference(resolution,[],[f13,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_setfam_1(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ~r1_setfam_1(sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0,X1] : (~r1_setfam_1(X0,X1) & r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 0.22/0.48    inference(negated_conjecture,[],[f6])).
% 0.22/0.48  fof(f6,conjecture,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X4] : (~r2_hidden(X4,sK0) | r2_hidden(X4,sK1)) )),
% 0.22/0.48    inference(superposition,[],[f28,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    sK0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.48    inference(resolution,[],[f12,f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    r1_tarski(sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(equality_resolution,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ~r2_hidden(sK2(sK0,sK1),sK1)),
% 0.22/0.48    inference(superposition,[],[f61,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.48    inference(rectify,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(k2_xboole_0(sK2(sK0,sK1),X0),sK1)) )),
% 0.22/0.48    inference(resolution,[],[f31,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_tarski(sK2(sK0,sK1),X0) | ~r2_hidden(X0,sK1)) )),
% 0.22/0.48    inference(resolution,[],[f13,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r1_tarski(sK2(X0,X1),X3) | r1_setfam_1(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (27091)------------------------------
% 0.22/0.48  % (27091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (27091)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (27091)Memory used [KB]: 1663
% 0.22/0.48  % (27091)Time elapsed: 0.053 s
% 0.22/0.48  % (27091)------------------------------
% 0.22/0.48  % (27091)------------------------------
% 0.22/0.48  % (27084)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (27077)Success in time 0.112 s
%------------------------------------------------------------------------------
