%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  68 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :   79 ( 187 expanded)
%              Number of equality atoms :   23 (  52 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(subsumption_resolution,[],[f91,f29])).

fof(f29,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k1_xboole_0 != sK0
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X0
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
   => ( k1_xboole_0 != sK0
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f91,plain,(
    k1_xboole_0 = sK0 ),
    inference(superposition,[],[f87,f63])).

fof(f63,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f62,f31])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f62,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f33,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f59,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f37,f30])).

fof(f30,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f59,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f33,f31])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f87,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK0) ),
    inference(resolution,[],[f78,f37])).

fof(f78,plain,(
    r1_xboole_0(sK0,sK0) ),
    inference(resolution,[],[f66,f72])).

fof(f72,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f67,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f67,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f65,f28])).

fof(f28,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK1,X0)
      | r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f39,f26])).

fof(f26,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f66,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(sK2,X1)
      | r1_xboole_0(sK0,X1) ) ),
    inference(resolution,[],[f39,f27])).

fof(f27,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (2800)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (2792)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (2792)Refutation not found, incomplete strategy% (2792)------------------------------
% 0.20/0.51  % (2792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (2784)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (2792)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (2792)Memory used [KB]: 6140
% 0.20/0.51  % (2792)Time elapsed: 0.058 s
% 0.20/0.51  % (2792)------------------------------
% 0.20/0.51  % (2792)------------------------------
% 0.20/0.51  % (2781)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (2782)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (2784)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f91,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    k1_xboole_0 != sK0),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    k1_xboole_0 != sK0 & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK2) & r1_tarski(sK0,sK1)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k1_xboole_0 != X0 & r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => (k1_xboole_0 != sK0 & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK2) & r1_tarski(sK0,sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k1_xboole_0 != X0 & r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k1_xboole_0 != X0 & (r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.20/0.51    inference(negated_conjecture,[],[f9])).
% 0.20/0.51  fof(f9,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    k1_xboole_0 = sK0),
% 0.20/0.51    inference(superposition,[],[f87,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.51    inference(forward_demodulation,[],[f62,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 0.20/0.51    inference(superposition,[],[f33,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f59,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(resolution,[],[f37,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.20/0.51    inference(superposition,[],[f33,f31])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    k1_xboole_0 = k3_xboole_0(sK0,sK0)),
% 0.20/0.51    inference(resolution,[],[f78,f37])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    r1_xboole_0(sK0,sK0)),
% 0.20/0.51    inference(resolution,[],[f66,f72])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    r1_xboole_0(sK2,sK0)),
% 0.20/0.51    inference(resolution,[],[f67,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    r1_xboole_0(sK0,sK2)),
% 0.20/0.51    inference(resolution,[],[f65,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    r1_xboole_0(sK1,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_xboole_0(sK1,X0) | r1_xboole_0(sK0,X0)) )),
% 0.20/0.51    inference(resolution,[],[f39,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X1] : (~r1_xboole_0(sK2,X1) | r1_xboole_0(sK0,X1)) )),
% 0.20/0.51    inference(resolution,[],[f39,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    r1_tarski(sK0,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (2784)------------------------------
% 0.20/0.51  % (2784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (2784)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (2784)Memory used [KB]: 6268
% 0.20/0.51  % (2784)Time elapsed: 0.073 s
% 0.20/0.51  % (2784)------------------------------
% 0.20/0.51  % (2784)------------------------------
% 0.20/0.51  % (2776)Success in time 0.154 s
%------------------------------------------------------------------------------
