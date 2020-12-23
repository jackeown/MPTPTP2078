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
% DateTime   : Thu Dec  3 12:40:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  59 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 127 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f209,plain,(
    $false ),
    inference(subsumption_resolution,[],[f208,f31])).

fof(f31,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1)
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f208,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f207,f32])).

fof(f32,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f207,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f200,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f200,plain,(
    ~ r1_tarski(k2_tarski(sK0,sK2),sK1) ),
    inference(trivial_inequality_removal,[],[f199])).

fof(f199,plain,
    ( k2_tarski(sK0,sK2) != k2_tarski(sK0,sK2)
    | ~ r1_tarski(k2_tarski(sK0,sK2),sK1) ),
    inference(superposition,[],[f33,f94])).

fof(f94,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = X1
      | ~ r1_tarski(X1,X2) ) ),
    inference(backward_demodulation,[],[f70,f88])).

fof(f88,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f66,f38])).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f66,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f65,f36])).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f65,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f59,f37])).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f59,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f41,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f70,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = k5_xboole_0(X1,k1_xboole_0)
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f69,f34])).

fof(f69,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,X2))
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f64,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f64,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f41,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f33,plain,(
    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:22:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (26255)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.42  % (26262)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.45  % (26256)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (26261)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (26253)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (26256)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f209,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f208,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    r2_hidden(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1) & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1) & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1) & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f20])).
% 0.21/0.47  fof(f20,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 0.21/0.47  fof(f208,plain,(
% 0.21/0.47    ~r2_hidden(sK0,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f207,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    r2_hidden(sK2,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f207,plain,(
% 0.21/0.47    ~r2_hidden(sK2,sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.47    inference(resolution,[],[f200,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.47    inference(flattening,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.47    inference(nnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    ~r1_tarski(k2_tarski(sK0,sK2),sK1)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f199])).
% 0.21/0.47  fof(f199,plain,(
% 0.21/0.47    k2_tarski(sK0,sK2) != k2_tarski(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK2),sK1)),
% 0.21/0.47    inference(superposition,[],[f33,f94])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = X1 | ~r1_tarski(X1,X2)) )),
% 0.21/0.47    inference(backward_demodulation,[],[f70,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.21/0.48    inference(superposition,[],[f66,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.48    inference(forward_demodulation,[],[f65,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.48    inference(rectify,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f59,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.48    inference(rectify,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 0.21/0.48    inference(superposition,[],[f41,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X1,X2)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f69,f34])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,X2)) | ~r1_tarski(X1,X2)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f64,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),X2) | ~r1_tarski(X1,X2)) )),
% 0.21/0.48    inference(superposition,[],[f41,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (26256)------------------------------
% 0.21/0.48  % (26256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (26256)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (26256)Memory used [KB]: 1791
% 0.21/0.48  % (26256)Time elapsed: 0.075 s
% 0.21/0.48  % (26256)------------------------------
% 0.21/0.48  % (26256)------------------------------
% 0.21/0.48  % (26252)Success in time 0.123 s
%------------------------------------------------------------------------------
