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
% DateTime   : Thu Dec  3 12:32:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   22 (  27 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   35 (  47 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,plain,(
    $false ),
    inference(resolution,[],[f38,f14])).

fof(f14,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f38,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),sK0) ),
    inference(superposition,[],[f33,f22])).

fof(f22,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f16,f12])).

fof(f12,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f33,plain,(
    ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f30,f15])).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f30,plain,(
    ! [X0] : ~ r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f17,f13])).

fof(f13,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n006.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 18:01:52 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.21/0.40  % (29015)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.40  % (29016)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.40  % (29017)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.40  % (29015)Refutation found. Thanks to Tanya!
% 0.21/0.40  % SZS status Theorem for theBenchmark
% 0.21/0.40  % SZS output start Proof for theBenchmark
% 0.21/0.40  fof(f39,plain,(
% 0.21/0.40    $false),
% 0.21/0.40    inference(resolution,[],[f38,f14])).
% 0.21/0.40  fof(f14,plain,(
% 0.21/0.40    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.40    inference(cnf_transformation,[],[f2])).
% 0.21/0.40  fof(f2,axiom,(
% 0.21/0.40    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.40  fof(f38,plain,(
% 0.21/0.40    ~r1_tarski(k3_xboole_0(sK0,sK2),sK0)),
% 0.21/0.40    inference(superposition,[],[f33,f22])).
% 0.21/0.40  fof(f22,plain,(
% 0.21/0.40    sK0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.40    inference(resolution,[],[f16,f12])).
% 0.21/0.40  fof(f12,plain,(
% 0.21/0.40    r1_tarski(sK0,sK1)),
% 0.21/0.40    inference(cnf_transformation,[],[f11])).
% 0.21/0.40  fof(f11,plain,(
% 0.21/0.40    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1)),
% 0.21/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).
% 0.21/0.40  fof(f10,plain,(
% 0.21/0.40    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,X2),X1) & r1_tarski(X0,X1)) => (~r1_tarski(k3_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1))),
% 0.21/0.40    introduced(choice_axiom,[])).
% 0.21/0.40  fof(f7,plain,(
% 0.21/0.40    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,X2),X1) & r1_tarski(X0,X1))),
% 0.21/0.40    inference(ennf_transformation,[],[f6])).
% 0.21/0.40  fof(f6,negated_conjecture,(
% 0.21/0.40    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.21/0.40    inference(negated_conjecture,[],[f5])).
% 0.21/0.40  fof(f5,conjecture,(
% 0.21/0.40    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.21/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.21/0.40  fof(f16,plain,(
% 0.21/0.40    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.40    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,sK1))) )),
% 0.21/0.41    inference(superposition,[],[f30,f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X0))) )),
% 0.21/0.41    inference(resolution,[],[f17,f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (29015)------------------------------
% 0.21/0.41  % (29015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (29015)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (29015)Memory used [KB]: 6012
% 0.21/0.41  % (29015)Time elapsed: 0.004 s
% 0.21/0.41  % (29015)------------------------------
% 0.21/0.41  % (29015)------------------------------
% 0.21/0.41  % (29010)Success in time 0.061 s
%------------------------------------------------------------------------------
