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
% DateTime   : Thu Dec  3 12:32:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  36 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   34 (  56 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f415,plain,(
    $false ),
    inference(resolution,[],[f399,f12])).

fof(f12,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).

fof(f9,plain,
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

fof(f399,plain,(
    ! [X4] : r1_tarski(k3_xboole_0(sK0,X4),sK1) ),
    inference(superposition,[],[f13,f106])).

fof(f106,plain,(
    ! [X24] : k3_xboole_0(sK0,X24) = k3_xboole_0(sK1,k3_xboole_0(sK0,X24)) ),
    inference(superposition,[],[f16,f76])).

fof(f76,plain,(
    sK0 = k3_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f52,f21])).

fof(f21,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f15,f11])).

fof(f11,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f15,plain,(
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

fof(f52,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f23,f14])).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f23,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X3) ),
    inference(resolution,[],[f15,f17])).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f13,f14])).

fof(f16,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f13,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (16607)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.43  % (16610)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.44  % (16609)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.44  % (16607)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f415,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(resolution,[],[f399,f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,X2),X1) & r1_tarski(X0,X1)) => (~r1_tarski(k3_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f7,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,X2),X1) & r1_tarski(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.20/0.44    inference(negated_conjecture,[],[f5])).
% 0.20/0.44  fof(f5,conjecture,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.20/0.44  fof(f399,plain,(
% 0.20/0.44    ( ! [X4] : (r1_tarski(k3_xboole_0(sK0,X4),sK1)) )),
% 0.20/0.44    inference(superposition,[],[f13,f106])).
% 0.20/0.44  fof(f106,plain,(
% 0.20/0.44    ( ! [X24] : (k3_xboole_0(sK0,X24) = k3_xboole_0(sK1,k3_xboole_0(sK0,X24))) )),
% 0.20/0.44    inference(superposition,[],[f16,f76])).
% 0.20/0.44  fof(f76,plain,(
% 0.20/0.44    sK0 = k3_xboole_0(sK1,sK0)),
% 0.20/0.44    inference(superposition,[],[f52,f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    sK0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.44    inference(resolution,[],[f15,f11])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    r1_tarski(sK0,sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f10])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4))) )),
% 0.20/0.44    inference(superposition,[],[f23,f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X3)) )),
% 0.20/0.44    inference(resolution,[],[f15,f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.20/0.44    inference(superposition,[],[f13,f14])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (16607)------------------------------
% 0.20/0.44  % (16607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (16611)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.44  % (16607)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (16607)Memory used [KB]: 6268
% 0.20/0.44  % (16607)Time elapsed: 0.011 s
% 0.20/0.44  % (16607)------------------------------
% 0.20/0.44  % (16607)------------------------------
% 0.20/0.44  % (16602)Success in time 0.087 s
%------------------------------------------------------------------------------
