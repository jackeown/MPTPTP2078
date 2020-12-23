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
% DateTime   : Thu Dec  3 12:29:38 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   20 (  23 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  36 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(subsumption_resolution,[],[f40,f11])).

fof(f11,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f40,plain,(
    r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f26,f10])).

fof(f10,plain,(
    r1_tarski(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k3_xboole_0(X0,X1))
      | r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f15,f18])).

fof(f18,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f17,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f14,f12])).

fof(f12,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:03:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.40  % (27659)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.14/0.41  % (27659)Refutation found. Thanks to Tanya!
% 0.14/0.41  % SZS status Theorem for theBenchmark
% 0.14/0.41  % SZS output start Proof for theBenchmark
% 0.14/0.41  fof(f43,plain,(
% 0.14/0.41    $false),
% 0.14/0.41    inference(subsumption_resolution,[],[f40,f11])).
% 0.14/0.41  fof(f11,plain,(
% 0.14/0.41    ~r1_tarski(sK0,sK1)),
% 0.14/0.41    inference(cnf_transformation,[],[f7])).
% 0.14/0.41  fof(f7,plain,(
% 0.14/0.41    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.14/0.41    inference(ennf_transformation,[],[f6])).
% 0.14/0.41  fof(f6,negated_conjecture,(
% 0.14/0.41    ~! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.14/0.41    inference(negated_conjecture,[],[f5])).
% 0.14/0.41  fof(f5,conjecture,(
% 0.14/0.41    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.14/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.14/0.41  fof(f40,plain,(
% 0.14/0.41    r1_tarski(sK0,sK1)),
% 0.14/0.41    inference(resolution,[],[f26,f10])).
% 0.14/0.41  fof(f10,plain,(
% 0.14/0.41    r1_tarski(sK0,k3_xboole_0(sK1,sK2))),
% 0.14/0.41    inference(cnf_transformation,[],[f7])).
% 0.14/0.41  fof(f26,plain,(
% 0.14/0.41    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_xboole_0(X0,X1)) | r1_tarski(X2,X0)) )),
% 0.14/0.41    inference(superposition,[],[f15,f18])).
% 0.14/0.41  fof(f18,plain,(
% 0.14/0.41    ( ! [X2,X3] : (k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2) )),
% 0.14/0.41    inference(superposition,[],[f17,f13])).
% 0.14/0.41  fof(f13,plain,(
% 0.14/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.14/0.41    inference(cnf_transformation,[],[f1])).
% 0.14/0.41  fof(f1,axiom,(
% 0.14/0.41    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.14/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.14/0.41  fof(f17,plain,(
% 0.14/0.41    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) )),
% 0.14/0.41    inference(resolution,[],[f14,f12])).
% 0.14/0.41  fof(f12,plain,(
% 0.14/0.41    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.14/0.41    inference(cnf_transformation,[],[f4])).
% 0.14/0.41  fof(f4,axiom,(
% 0.14/0.41    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.14/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.14/0.41  fof(f14,plain,(
% 0.14/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.14/0.41    inference(cnf_transformation,[],[f8])).
% 0.14/0.41  fof(f8,plain,(
% 0.14/0.41    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.14/0.41    inference(ennf_transformation,[],[f3])).
% 0.14/0.41  fof(f3,axiom,(
% 0.14/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.14/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.14/0.41  fof(f15,plain,(
% 0.14/0.41    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.14/0.41    inference(cnf_transformation,[],[f9])).
% 0.14/0.41  fof(f9,plain,(
% 0.14/0.41    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.14/0.41    inference(ennf_transformation,[],[f2])).
% 0.14/0.41  fof(f2,axiom,(
% 0.14/0.41    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.14/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.14/0.41  % SZS output end Proof for theBenchmark
% 0.14/0.41  % (27659)------------------------------
% 0.14/0.41  % (27659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.41  % (27659)Termination reason: Refutation
% 0.14/0.41  
% 0.14/0.41  % (27659)Memory used [KB]: 10490
% 0.14/0.41  % (27659)Time elapsed: 0.003 s
% 0.14/0.41  % (27659)------------------------------
% 0.14/0.41  % (27659)------------------------------
% 0.20/0.41  % (27655)Success in time 0.05 s
%------------------------------------------------------------------------------
