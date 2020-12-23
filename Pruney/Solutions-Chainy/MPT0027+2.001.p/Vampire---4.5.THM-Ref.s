%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  56 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :   12
%              Number of atoms          :   85 ( 219 expanded)
%              Number of equality atoms :   19 (  43 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(subsumption_resolution,[],[f249,f18])).

fof(f18,plain,(
    sK0 != k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK0 != k3_xboole_0(sK1,sK2)
    & ! [X3] :
        ( r1_tarski(X3,sK0)
        | ~ r1_tarski(X3,sK2)
        | ~ r1_tarski(X3,sK1) )
    & r1_tarski(sK0,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X1,X2) != X0
        & ! [X3] :
            ( r1_tarski(X3,X0)
            | ~ r1_tarski(X3,X2)
            | ~ r1_tarski(X3,X1) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
   => ( sK0 != k3_xboole_0(sK1,sK2)
      & ! [X3] :
          ( r1_tarski(X3,sK0)
          | ~ r1_tarski(X3,sK2)
          | ~ r1_tarski(X3,sK1) )
      & r1_tarski(sK0,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( r1_tarski(X3,X0)
          | ~ r1_tarski(X3,X2)
          | ~ r1_tarski(X3,X1) )
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( r1_tarski(X3,X0)
          | ~ r1_tarski(X3,X2)
          | ~ r1_tarski(X3,X1) )
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( ( r1_tarski(X3,X2)
                & r1_tarski(X3,X1) )
             => r1_tarski(X3,X0) )
          & r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X1,X2) = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f249,plain,(
    sK0 = k3_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f75,f245])).

fof(f245,plain,(
    sK0 = k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f132,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f132,plain,(
    sK0 = k2_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    inference(resolution,[],[f127,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f127,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),sK0) ),
    inference(resolution,[],[f58,f19])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f58,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_xboole_0(X0,sK2),sK1)
      | r1_tarski(k3_xboole_0(X0,sK2),sK0) ) ),
    inference(superposition,[],[f30,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f30,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_xboole_0(sK2,X0),sK1)
      | r1_tarski(k3_xboole_0(sK2,X0),sK0) ) ),
    inference(resolution,[],[f17,f19])).

fof(f17,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK2)
      | r1_tarski(X3,sK0)
      | ~ r1_tarski(X3,sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f75,plain,(
    k3_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f37,f22])).

fof(f37,plain,(
    r1_tarski(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f24,f16])).

fof(f16,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | r1_tarski(sK0,k3_xboole_0(sK1,X0)) ) ),
    inference(resolution,[],[f15,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (30068)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.46  % (30074)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (30074)Refutation not found, incomplete strategy% (30074)------------------------------
% 0.20/0.46  % (30074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (30074)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (30074)Memory used [KB]: 1663
% 0.20/0.46  % (30074)Time elapsed: 0.062 s
% 0.20/0.46  % (30074)------------------------------
% 0.20/0.46  % (30074)------------------------------
% 0.20/0.47  % (30066)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (30075)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (30073)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (30073)Refutation not found, incomplete strategy% (30073)------------------------------
% 0.20/0.47  % (30073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (30073)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (30073)Memory used [KB]: 6012
% 0.20/0.47  % (30073)Time elapsed: 0.001 s
% 0.20/0.47  % (30073)------------------------------
% 0.20/0.47  % (30073)------------------------------
% 0.20/0.47  % (30076)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (30065)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (30065)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f250,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f249,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    sK0 != k3_xboole_0(sK1,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    sK0 != k3_xboole_0(sK1,sK2) & ! [X3] : (r1_tarski(X3,sK0) | ~r1_tarski(X3,sK2) | ~r1_tarski(X3,sK1)) & r1_tarski(sK0,sK2) & r1_tarski(sK0,sK1)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k3_xboole_0(X1,X2) != X0 & ! [X3] : (r1_tarski(X3,X0) | ~r1_tarski(X3,X2) | ~r1_tarski(X3,X1)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => (sK0 != k3_xboole_0(sK1,sK2) & ! [X3] : (r1_tarski(X3,sK0) | ~r1_tarski(X3,sK2) | ~r1_tarski(X3,sK1)) & r1_tarski(sK0,sK2) & r1_tarski(sK0,sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k3_xboole_0(X1,X2) != X0 & ! [X3] : (r1_tarski(X3,X0) | ~r1_tarski(X3,X2) | ~r1_tarski(X3,X1)) & r1_tarski(X0,X2) & r1_tarski(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k3_xboole_0(X1,X2) != X0 & (! [X3] : (r1_tarski(X3,X0) | (~r1_tarski(X3,X2) | ~r1_tarski(X3,X1))) & r1_tarski(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 0.20/0.48    inference(negated_conjecture,[],[f6])).
% 0.20/0.48  fof(f6,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).
% 0.20/0.48  fof(f249,plain,(
% 0.20/0.48    sK0 = k3_xboole_0(sK1,sK2)),
% 0.20/0.48    inference(backward_demodulation,[],[f75,f245])).
% 0.20/0.48  fof(f245,plain,(
% 0.20/0.48    sK0 = k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.48    inference(superposition,[],[f132,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    sK0 = k2_xboole_0(k3_xboole_0(sK1,sK2),sK0)),
% 0.20/0.48    inference(resolution,[],[f127,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    r1_tarski(k3_xboole_0(sK1,sK2),sK0)),
% 0.20/0.48    inference(resolution,[],[f58,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(k3_xboole_0(X0,sK2),sK1) | r1_tarski(k3_xboole_0(X0,sK2),sK0)) )),
% 0.20/0.48    inference(superposition,[],[f30,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(k3_xboole_0(sK2,X0),sK1) | r1_tarski(k3_xboole_0(sK2,X0),sK0)) )),
% 0.20/0.48    inference(resolution,[],[f17,f19])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ( ! [X3] : (~r1_tarski(X3,sK2) | r1_tarski(X3,sK0) | ~r1_tarski(X3,sK1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    k3_xboole_0(sK1,sK2) = k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.48    inference(resolution,[],[f37,f22])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    r1_tarski(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.48    inference(resolution,[],[f24,f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    r1_tarski(sK0,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(sK0,X0) | r1_tarski(sK0,k3_xboole_0(sK1,X0))) )),
% 0.20/0.48    inference(resolution,[],[f15,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    r1_tarski(sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (30065)------------------------------
% 0.20/0.48  % (30065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (30065)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (30065)Memory used [KB]: 1791
% 0.20/0.48  % (30065)Time elapsed: 0.074 s
% 0.20/0.48  % (30065)------------------------------
% 0.20/0.48  % (30065)------------------------------
% 0.20/0.49  % (30059)Success in time 0.132 s
%------------------------------------------------------------------------------
