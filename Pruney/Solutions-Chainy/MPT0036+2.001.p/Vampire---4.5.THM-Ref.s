%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    5
%              Number of atoms          :   18 (  18 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,plain,(
    $false ),
    inference(subsumption_resolution,[],[f15,f9])).

fof(f9,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f15,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f13,f8])).

fof(f8,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] : ~ r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k2_xboole_0(X1,X0))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f11,f10])).

fof(f10,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:00:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.38  % (21833)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.38  % (21833)Refutation found. Thanks to Tanya!
% 0.20/0.38  % SZS status Theorem for theBenchmark
% 0.20/0.38  % SZS output start Proof for theBenchmark
% 0.20/0.38  fof(f18,plain,(
% 0.20/0.38    $false),
% 0.20/0.38    inference(subsumption_resolution,[],[f15,f9])).
% 0.20/0.38  fof(f9,plain,(
% 0.20/0.38    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.38    inference(cnf_transformation,[],[f3])).
% 0.20/0.38  fof(f3,axiom,(
% 0.20/0.38    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.38  fof(f15,plain,(
% 0.20/0.38    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0)),
% 0.20/0.38    inference(resolution,[],[f13,f8])).
% 0.20/0.38  fof(f8,plain,(
% 0.20/0.38    ~r1_tarski(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 0.20/0.38    inference(cnf_transformation,[],[f6])).
% 0.20/0.38  fof(f6,plain,(
% 0.20/0.38    ? [X0,X1,X2] : ~r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.20/0.38    inference(ennf_transformation,[],[f5])).
% 0.20/0.38  fof(f5,negated_conjecture,(
% 0.20/0.38    ~! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.20/0.38    inference(negated_conjecture,[],[f4])).
% 0.20/0.38  fof(f4,conjecture,(
% 0.20/0.38    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.20/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).
% 0.20/0.38  fof(f13,plain,(
% 0.20/0.38    ( ! [X2,X0,X1] : (r1_tarski(X2,k2_xboole_0(X1,X0)) | ~r1_tarski(X2,X1)) )),
% 0.20/0.38    inference(superposition,[],[f11,f10])).
% 0.20/0.38  fof(f10,plain,(
% 0.20/0.38    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.38    inference(cnf_transformation,[],[f1])).
% 0.20/0.38  fof(f1,axiom,(
% 0.20/0.38    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.38  fof(f11,plain,(
% 0.20/0.38    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.38    inference(cnf_transformation,[],[f7])).
% 0.20/0.38  fof(f7,plain,(
% 0.20/0.38    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.38    inference(ennf_transformation,[],[f2])).
% 0.20/0.38  fof(f2,axiom,(
% 0.20/0.38    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.20/0.38    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.20/0.38  % SZS output end Proof for theBenchmark
% 0.20/0.38  % (21833)------------------------------
% 0.20/0.38  % (21833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.38  % (21833)Termination reason: Refutation
% 0.20/0.38  
% 0.20/0.38  % (21833)Memory used [KB]: 10490
% 0.20/0.38  % (21833)Time elapsed: 0.003 s
% 0.20/0.38  % (21833)------------------------------
% 0.20/0.38  % (21833)------------------------------
% 0.20/0.38  % (21830)Success in time 0.035 s
%------------------------------------------------------------------------------
