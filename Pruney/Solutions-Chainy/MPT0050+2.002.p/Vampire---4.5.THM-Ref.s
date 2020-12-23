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
% DateTime   : Thu Dec  3 12:29:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  30 expanded)
%              Number of leaves         :    7 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  55 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(subsumption_resolution,[],[f85,f16])).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f85,plain,(
    ~ r1_tarski(k4_xboole_0(sK2,sK1),sK2) ),
    inference(forward_demodulation,[],[f76,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f18,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f76,plain,(
    ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK1,sK2),sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f15,f59,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f59,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),k4_xboole_0(k2_xboole_0(sK1,sK2),X0)) ),
    inference(unit_resulting_resolution,[],[f14,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

fof(f14,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k2_xboole_0(X1,X2))
       => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f15,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (28990)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.42  % (28989)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.42  % (28992)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (28994)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (28990)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(subsumption_resolution,[],[f85,f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    ~r1_tarski(k4_xboole_0(sK2,sK1),sK2)),
% 0.21/0.42    inference(forward_demodulation,[],[f76,f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 0.21/0.42    inference(superposition,[],[f18,f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK1,sK2),sK1),sK2)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f15,f59,f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(flattening,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,X0),k4_xboole_0(k2_xboole_0(sK1,sK2),X0))) )),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f14,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ~r1_tarski(k4_xboole_0(sK0,sK1),sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X0,X1),X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(k4_xboole_0(sK0,sK1),sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X0,X1),X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.42    inference(negated_conjecture,[],[f6])).
% 0.21/0.42  fof(f6,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ~r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (28990)------------------------------
% 0.21/0.42  % (28990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (28990)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (28990)Memory used [KB]: 6140
% 0.21/0.42  % (28990)Time elapsed: 0.006 s
% 0.21/0.42  % (28990)------------------------------
% 0.21/0.42  % (28990)------------------------------
% 0.21/0.43  % (28988)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.43  % (28987)Success in time 0.075 s
%------------------------------------------------------------------------------
