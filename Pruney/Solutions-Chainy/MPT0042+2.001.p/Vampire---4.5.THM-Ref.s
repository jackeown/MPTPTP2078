%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:48 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   28 (  36 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  75 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(subsumption_resolution,[],[f100,f15])).

fof(f15,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).

fof(f100,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(resolution,[],[f96,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f96,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f94,f16])).

fof(f16,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k4_xboole_0(sK1,X0))
      | ~ r1_tarski(X1,k4_xboole_0(sK0,X0)) ) ),
    inference(superposition,[],[f25,f68])).

fof(f68,plain,(
    ! [X26] : k4_xboole_0(sK1,X26) = k2_xboole_0(k4_xboole_0(sK0,X26),k4_xboole_0(sK1,X26)) ),
    inference(resolution,[],[f35,f14])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f20,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k2_xboole_0(X1,X0))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f19,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.40  % (12853)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.19/0.40  % (12847)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.19/0.41  % (12851)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.19/0.42  % (12846)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.19/0.42  % (12846)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f101,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(subsumption_resolution,[],[f100,f15])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    r1_tarski(sK2,sK3)),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    ? [X0,X1,X2,X3] : (~r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.19/0.42    inference(flattening,[],[f8])).
% 0.19/0.42  fof(f8,plain,(
% 0.19/0.42    ? [X0,X1,X2,X3] : (~r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.19/0.42    inference(ennf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,negated_conjecture,(
% 0.19/0.42    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)))),
% 0.19/0.42    inference(negated_conjecture,[],[f6])).
% 0.19/0.42  fof(f6,conjecture,(
% 0.19/0.42    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).
% 0.19/0.42  fof(f100,plain,(
% 0.19/0.42    ~r1_tarski(sK2,sK3)),
% 0.19/0.42    inference(resolution,[],[f96,f21])).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f13])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 0.19/0.42  fof(f96,plain,(
% 0.19/0.42    ~r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK0,sK2))),
% 0.19/0.42    inference(resolution,[],[f94,f16])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ~r1_tarski(k4_xboole_0(sK0,sK3),k4_xboole_0(sK1,sK2))),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  fof(f94,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_tarski(X1,k4_xboole_0(sK1,X0)) | ~r1_tarski(X1,k4_xboole_0(sK0,X0))) )),
% 0.19/0.42    inference(superposition,[],[f25,f68])).
% 0.19/0.42  fof(f68,plain,(
% 0.19/0.42    ( ! [X26] : (k4_xboole_0(sK1,X26) = k2_xboole_0(k4_xboole_0(sK0,X26),k4_xboole_0(sK1,X26))) )),
% 0.19/0.42    inference(resolution,[],[f35,f14])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    r1_tarski(sK0,sK1)),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  fof(f35,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.19/0.42    inference(resolution,[],[f20,f18])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.19/0.42    inference(cnf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,plain,(
% 0.19/0.42    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f12])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (r1_tarski(X2,k2_xboole_0(X1,X0)) | ~r1_tarski(X2,X1)) )),
% 0.19/0.42    inference(superposition,[],[f19,f17])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f11])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (12846)------------------------------
% 0.19/0.42  % (12846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (12846)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (12846)Memory used [KB]: 10618
% 0.19/0.42  % (12846)Time elapsed: 0.008 s
% 0.19/0.42  % (12846)------------------------------
% 0.19/0.42  % (12846)------------------------------
% 0.19/0.43  % (12845)Success in time 0.077 s
%------------------------------------------------------------------------------
