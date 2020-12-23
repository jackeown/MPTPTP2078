%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   17 (  20 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  36 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23,f9])).

fof(f9,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k2_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f23,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f22,f11])).

fof(f11,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f22,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,X0) ) ),
    inference(forward_demodulation,[],[f20,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f20,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(sK2,sK1))
      | ~ r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f13,f10])).

fof(f10,plain,(
    ~ r1_tarski(sK0,k2_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:27:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (29610)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.42  % (29617)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.42  % (29610)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(subsumption_resolution,[],[f23,f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    r1_tarski(sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (~r1_tarski(X0,k2_xboole_0(X2,X1)) & r1_tarski(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.20/0.42    inference(negated_conjecture,[],[f4])).
% 0.20/0.42  fof(f4,conjecture,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ~r1_tarski(sK0,sK1)),
% 0.20/0.42    inference(resolution,[],[f22,f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK0,X0)) )),
% 0.20/0.42    inference(forward_demodulation,[],[f20,f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK2,sK1)) | ~r1_tarski(sK0,X0)) )),
% 0.20/0.42    inference(resolution,[],[f13,f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ~r1_tarski(sK0,k2_xboole_0(sK2,sK1))),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(flattening,[],[f7])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (29610)------------------------------
% 0.20/0.42  % (29610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (29610)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (29610)Memory used [KB]: 10490
% 0.20/0.42  % (29610)Time elapsed: 0.005 s
% 0.20/0.42  % (29610)------------------------------
% 0.20/0.42  % (29610)------------------------------
% 0.20/0.43  % (29609)Success in time 0.071 s
%------------------------------------------------------------------------------
