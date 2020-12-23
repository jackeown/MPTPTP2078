%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   25 (  42 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :   10
%              Number of atoms          :   49 (  95 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(subsumption_resolution,[],[f35,f22])).

fof(f22,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f35,plain,(
    r2_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f15,f33])).

fof(f33,plain,(
    sK0 = sK1 ),
    inference(backward_demodulation,[],[f24,f29])).

fof(f29,plain,(
    sK0 = k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f27,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f27,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f25,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f25,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f15,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f14,f18])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( r2_xboole_0(sK1,sK0)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) )
   => ( r2_xboole_0(sK1,sK0)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( r2_xboole_0(X1,X0)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r2_xboole_0(X1,X0)
          & r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f15,plain,(
    r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:45:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (9430)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (9424)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (9424)Refutation not found, incomplete strategy% (9424)------------------------------
% 0.22/0.48  % (9424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (9424)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (9424)Memory used [KB]: 10490
% 0.22/0.48  % (9424)Time elapsed: 0.071 s
% 0.22/0.48  % (9424)------------------------------
% 0.22/0.48  % (9424)------------------------------
% 0.22/0.49  % (9436)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (9436)Refutation not found, incomplete strategy% (9436)------------------------------
% 0.22/0.49  % (9436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (9436)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (9436)Memory used [KB]: 6012
% 0.22/0.49  % (9436)Time elapsed: 0.003 s
% 0.22/0.49  % (9436)------------------------------
% 0.22/0.49  % (9436)------------------------------
% 0.22/0.50  % (9427)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (9427)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f35,f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    r2_xboole_0(sK0,sK0)),
% 0.22/0.50    inference(backward_demodulation,[],[f15,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    sK0 = sK1),
% 0.22/0.50    inference(backward_demodulation,[],[f24,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    sK0 = k2_xboole_0(sK0,sK1)),
% 0.22/0.50    inference(superposition,[],[f27,f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    sK0 = k2_xboole_0(sK1,sK0)),
% 0.22/0.50    inference(resolution,[],[f25,f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    r1_tarski(sK1,sK0)),
% 0.22/0.50    inference(resolution,[],[f15,f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.50    inference(resolution,[],[f14,f18])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    r1_tarski(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    r2_xboole_0(sK1,sK0) & r1_tarski(sK0,sK1)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0,X1] : (r2_xboole_0(X1,X0) & r1_tarski(X0,X1)) => (r2_xboole_0(sK1,sK0) & r1_tarski(sK0,sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ? [X0,X1] : (r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.22/0.50    inference(negated_conjecture,[],[f5])).
% 0.22/0.50  fof(f5,conjecture,(
% 0.22/0.50    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    r2_xboole_0(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (9427)------------------------------
% 0.22/0.50  % (9427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (9427)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (9427)Memory used [KB]: 1535
% 0.22/0.50  % (9427)Time elapsed: 0.089 s
% 0.22/0.50  % (9427)------------------------------
% 0.22/0.50  % (9427)------------------------------
% 0.22/0.50  % (9419)Success in time 0.143 s
%------------------------------------------------------------------------------
