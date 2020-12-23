%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:32 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   34 (  47 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :   12
%              Number of atoms          :   51 (  65 expanded)
%              Number of equality atoms :   39 (  53 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(subsumption_resolution,[],[f191,f41])).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f191,plain,(
    k1_tarski(sK0) != k2_tarski(sK0,sK0) ),
    inference(forward_demodulation,[],[f185,f65])).

fof(f65,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f63,f40])).

fof(f40,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f63,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = k2_xboole_0(X0,X0) ),
    inference(superposition,[],[f47,f41])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f185,plain,(
    k2_tarski(sK0,sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f64,f183])).

fof(f183,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f182,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f182,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f181])).

fof(f181,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | sK0 = sK1 ),
    inference(superposition,[],[f177,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f177,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f64,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X1,X0) = k5_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f50,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f64,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f39,f47])).

fof(f39,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f32])).

fof(f32,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:33:26 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.47  % (10063)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.23/0.48  % (10062)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.23/0.48  % (10055)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.48  % (10072)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.23/0.49  % (10060)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.49  % (10069)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.49  % (10064)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.23/0.49  % (10059)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.50  % (10056)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.23/0.50  % (10057)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.50  % (10068)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.50  % (10065)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.50  % (10058)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.50  % (10061)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.50  % (10058)Refutation found. Thanks to Tanya!
% 0.23/0.50  % SZS status Theorem for theBenchmark
% 0.23/0.50  % SZS output start Proof for theBenchmark
% 0.23/0.50  fof(f192,plain,(
% 0.23/0.50    $false),
% 0.23/0.50    inference(subsumption_resolution,[],[f191,f41])).
% 0.23/0.50  fof(f41,plain,(
% 0.23/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f11])).
% 0.23/0.50  fof(f11,axiom,(
% 0.23/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.50  fof(f191,plain,(
% 0.23/0.50    k1_tarski(sK0) != k2_tarski(sK0,sK0)),
% 0.23/0.50    inference(forward_demodulation,[],[f185,f65])).
% 0.23/0.50  fof(f65,plain,(
% 0.23/0.50    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.23/0.50    inference(forward_demodulation,[],[f63,f40])).
% 0.23/0.50  fof(f40,plain,(
% 0.23/0.50    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 0.23/0.50    inference(cnf_transformation,[],[f21])).
% 0.23/0.50  fof(f21,axiom,(
% 0.23/0.50    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 0.23/0.50  fof(f63,plain,(
% 0.23/0.50    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = k2_xboole_0(X0,X0)) )),
% 0.23/0.50    inference(superposition,[],[f47,f41])).
% 0.23/0.50  fof(f47,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f17])).
% 0.23/0.50  fof(f17,axiom,(
% 0.23/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.23/0.50  fof(f185,plain,(
% 0.23/0.50    k2_tarski(sK0,sK0) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.23/0.50    inference(backward_demodulation,[],[f64,f183])).
% 0.23/0.50  fof(f183,plain,(
% 0.23/0.50    sK0 = sK1),
% 0.23/0.50    inference(subsumption_resolution,[],[f182,f54])).
% 0.23/0.50  fof(f54,plain,(
% 0.23/0.50    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.23/0.50    inference(cnf_transformation,[],[f29])).
% 0.23/0.50  fof(f29,plain,(
% 0.23/0.50    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.23/0.50    inference(ennf_transformation,[],[f18])).
% 0.23/0.50  fof(f18,axiom,(
% 0.23/0.50    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.23/0.50  fof(f182,plain,(
% 0.23/0.50    ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | sK0 = sK1),
% 0.23/0.50    inference(trivial_inequality_removal,[],[f181])).
% 0.23/0.50  fof(f181,plain,(
% 0.23/0.50    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | sK0 = sK1),
% 0.23/0.50    inference(superposition,[],[f177,f55])).
% 0.23/0.50  fof(f55,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.23/0.50    inference(cnf_transformation,[],[f30])).
% 0.23/0.50  fof(f30,plain,(
% 0.23/0.50    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.23/0.50    inference(ennf_transformation,[],[f20])).
% 0.23/0.50  fof(f20,axiom,(
% 0.23/0.50    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 0.23/0.50  fof(f177,plain,(
% 0.23/0.50    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.23/0.50    inference(superposition,[],[f64,f95])).
% 0.23/0.50  fof(f95,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k5_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.23/0.50    inference(superposition,[],[f50,f57])).
% 0.23/0.50  fof(f57,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f38])).
% 0.23/0.50  fof(f38,plain,(
% 0.23/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.23/0.50    inference(nnf_transformation,[],[f9])).
% 0.23/0.50  fof(f9,axiom,(
% 0.23/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.23/0.50  fof(f50,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f10])).
% 0.23/0.50  fof(f10,axiom,(
% 0.23/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.23/0.50  fof(f64,plain,(
% 0.23/0.50    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.23/0.50    inference(superposition,[],[f39,f47])).
% 0.23/0.50  fof(f39,plain,(
% 0.23/0.50    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.23/0.50    inference(cnf_transformation,[],[f33])).
% 0.23/0.50  fof(f33,plain,(
% 0.23/0.50    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f32])).
% 0.23/0.50  fof(f32,plain,(
% 0.23/0.50    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f26,plain,(
% 0.23/0.50    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.23/0.50    inference(ennf_transformation,[],[f23])).
% 0.23/0.50  fof(f23,negated_conjecture,(
% 0.23/0.50    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.23/0.50    inference(negated_conjecture,[],[f22])).
% 0.23/0.50  fof(f22,conjecture,(
% 0.23/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 0.23/0.50  % SZS output end Proof for theBenchmark
% 0.23/0.50  % (10058)------------------------------
% 0.23/0.50  % (10058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (10058)Termination reason: Refutation
% 0.23/0.50  
% 0.23/0.50  % (10058)Memory used [KB]: 1663
% 0.23/0.50  % (10058)Time elapsed: 0.082 s
% 0.23/0.50  % (10058)------------------------------
% 0.23/0.50  % (10058)------------------------------
% 0.23/0.51  % (10053)Success in time 0.136 s
%------------------------------------------------------------------------------
