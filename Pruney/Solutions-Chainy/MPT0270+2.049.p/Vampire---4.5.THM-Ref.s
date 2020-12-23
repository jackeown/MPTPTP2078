%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:03 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 220 expanded)
%              Number of leaves         :    9 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :   89 ( 571 expanded)
%              Number of equality atoms :   46 ( 252 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(subsumption_resolution,[],[f82,f70])).

% (25554)Termination reason: Refutation not found, incomplete strategy
fof(f70,plain,(
    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f56,f66])).

% (25554)Memory used [KB]: 6140
% (25554)Time elapsed: 0.084 s
% (25554)------------------------------
% (25554)------------------------------
fof(f66,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f59,f64])).

fof(f64,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f62,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f62,plain,(
    r1_tarski(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f61,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f61,plain,(
    r2_hidden(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f60])).

fof(f60,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f33,f59])).

fof(f33,plain,
    ( r2_hidden(sK0,sK1)
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( r2_hidden(sK0,sK1)
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( ~ r2_hidden(sK0,sK1)
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
        & ( ~ r2_hidden(X0,X1)
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( r2_hidden(sK0,sK1)
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( ~ r2_hidden(sK0,sK1)
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f59,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(subsumption_resolution,[],[f58,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f58,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)
    | r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f32,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f32,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f82,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f80,f69])).

fof(f69,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f65,f66])).

fof(f65,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f62,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f80,plain,(
    k3_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f40,f67])).

fof(f67,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f64,f66])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.46/0.56  % (25545)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.46/0.57  % (25541)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.46/0.57  % (25562)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.46/0.57  % (25554)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.46/0.57  % (25553)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.46/0.57  % (25562)Refutation found. Thanks to Tanya!
% 1.46/0.57  % SZS status Theorem for theBenchmark
% 1.46/0.57  % (25554)Refutation not found, incomplete strategy% (25554)------------------------------
% 1.46/0.57  % (25554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % SZS output start Proof for theBenchmark
% 1.46/0.57  fof(f83,plain,(
% 1.46/0.57    $false),
% 1.46/0.57    inference(subsumption_resolution,[],[f82,f70])).
% 1.46/0.57  % (25554)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.57  fof(f70,plain,(
% 1.46/0.57    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.46/0.57    inference(superposition,[],[f56,f66])).
% 1.46/0.57  
% 1.46/0.57  % (25554)Memory used [KB]: 6140
% 1.46/0.57  % (25554)Time elapsed: 0.084 s
% 1.46/0.57  % (25554)------------------------------
% 1.46/0.57  % (25554)------------------------------
% 1.46/0.57  fof(f66,plain,(
% 1.46/0.57    k1_xboole_0 = k1_tarski(sK0)),
% 1.46/0.57    inference(backward_demodulation,[],[f59,f64])).
% 1.46/0.57  fof(f64,plain,(
% 1.46/0.57    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.46/0.57    inference(resolution,[],[f62,f49])).
% 1.46/0.57  fof(f49,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f30])).
% 1.46/0.57  fof(f30,plain,(
% 1.46/0.57    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.46/0.57    inference(nnf_transformation,[],[f3])).
% 1.46/0.57  fof(f3,axiom,(
% 1.46/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.46/0.57  fof(f62,plain,(
% 1.46/0.57    r1_tarski(k1_tarski(sK0),sK1)),
% 1.46/0.57    inference(resolution,[],[f61,f47])).
% 1.46/0.57  fof(f47,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f29])).
% 1.46/0.57  fof(f29,plain,(
% 1.46/0.57    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.46/0.57    inference(nnf_transformation,[],[f16])).
% 1.46/0.57  fof(f16,axiom,(
% 1.46/0.57    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.46/0.57  fof(f61,plain,(
% 1.46/0.57    r2_hidden(sK0,sK1)),
% 1.46/0.57    inference(trivial_inequality_removal,[],[f60])).
% 1.46/0.57  fof(f60,plain,(
% 1.46/0.57    k1_tarski(sK0) != k1_tarski(sK0) | r2_hidden(sK0,sK1)),
% 1.46/0.57    inference(backward_demodulation,[],[f33,f59])).
% 1.46/0.57  fof(f33,plain,(
% 1.46/0.57    r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.46/0.57    inference(cnf_transformation,[],[f27])).
% 1.46/0.57  fof(f27,plain,(
% 1.46/0.57    (r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.46/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f26])).
% 1.46/0.57  fof(f26,plain,(
% 1.46/0.57    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))) => ((r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.58  fof(f25,plain,(
% 1.46/0.58    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.46/0.58    inference(nnf_transformation,[],[f22])).
% 1.46/0.58  fof(f22,plain,(
% 1.46/0.58    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 1.46/0.58    inference(ennf_transformation,[],[f20])).
% 1.46/0.58  fof(f20,negated_conjecture,(
% 1.46/0.58    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.46/0.58    inference(negated_conjecture,[],[f19])).
% 1.46/0.58  fof(f19,conjecture,(
% 1.46/0.58    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.46/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.46/0.58  fof(f59,plain,(
% 1.46/0.58    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.46/0.58    inference(subsumption_resolution,[],[f58,f44])).
% 1.46/0.58  fof(f44,plain,(
% 1.46/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f28])).
% 1.46/0.58  fof(f28,plain,(
% 1.46/0.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.46/0.58    inference(nnf_transformation,[],[f9])).
% 1.46/0.58  fof(f9,axiom,(
% 1.46/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.46/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.46/0.58  fof(f58,plain,(
% 1.46/0.58    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) | r1_xboole_0(k1_tarski(sK0),sK1)),
% 1.46/0.58    inference(resolution,[],[f32,f42])).
% 1.46/0.58  fof(f42,plain,(
% 1.46/0.58    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f23])).
% 1.46/0.58  fof(f23,plain,(
% 1.46/0.58    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.46/0.58    inference(ennf_transformation,[],[f17])).
% 1.46/0.58  fof(f17,axiom,(
% 1.46/0.58    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.46/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.46/0.58  fof(f32,plain,(
% 1.46/0.58    ~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.46/0.58    inference(cnf_transformation,[],[f27])).
% 1.46/0.58  fof(f56,plain,(
% 1.46/0.58    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 1.46/0.58    inference(equality_resolution,[],[f50])).
% 1.46/0.58  fof(f50,plain,(
% 1.46/0.58    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.46/0.58    inference(cnf_transformation,[],[f31])).
% 1.46/0.58  fof(f31,plain,(
% 1.46/0.58    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.46/0.58    inference(nnf_transformation,[],[f18])).
% 1.46/0.58  fof(f18,axiom,(
% 1.46/0.58    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.46/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.46/0.58  fof(f82,plain,(
% 1.46/0.58    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.46/0.58    inference(forward_demodulation,[],[f80,f69])).
% 1.46/0.58  fof(f69,plain,(
% 1.46/0.58    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)),
% 1.46/0.58    inference(forward_demodulation,[],[f65,f66])).
% 1.46/0.58  fof(f65,plain,(
% 1.46/0.58    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 1.46/0.58    inference(resolution,[],[f62,f43])).
% 1.46/0.58  fof(f43,plain,(
% 1.46/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f24])).
% 1.46/0.58  fof(f24,plain,(
% 1.46/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.46/0.58    inference(ennf_transformation,[],[f5])).
% 1.46/0.58  fof(f5,axiom,(
% 1.46/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.46/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.46/0.58  fof(f80,plain,(
% 1.46/0.58    k3_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.46/0.58    inference(superposition,[],[f40,f67])).
% 1.46/0.58  fof(f67,plain,(
% 1.46/0.58    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 1.46/0.58    inference(backward_demodulation,[],[f64,f66])).
% 1.46/0.58  fof(f40,plain,(
% 1.46/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.46/0.58    inference(cnf_transformation,[],[f7])).
% 1.46/0.58  fof(f7,axiom,(
% 1.46/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.46/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.46/0.58  % SZS output end Proof for theBenchmark
% 1.46/0.58  % (25562)------------------------------
% 1.46/0.58  % (25562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.58  % (25562)Termination reason: Refutation
% 1.46/0.58  
% 1.46/0.58  % (25562)Memory used [KB]: 1791
% 1.46/0.58  % (25562)Time elapsed: 0.078 s
% 1.46/0.58  % (25562)------------------------------
% 1.46/0.58  % (25562)------------------------------
% 1.46/0.58  % (25546)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.46/0.58  % (25538)Success in time 0.219 s
%------------------------------------------------------------------------------
