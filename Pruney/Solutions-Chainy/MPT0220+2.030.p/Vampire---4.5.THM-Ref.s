%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:41 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 171 expanded)
%              Number of leaves         :   14 (  56 expanded)
%              Depth                    :   21
%              Number of atoms          :   61 ( 175 expanded)
%              Number of equality atoms :   55 ( 169 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f290,plain,(
    $false ),
    inference(subsumption_resolution,[],[f27,f287])).

fof(f287,plain,(
    ! [X8,X7] : k2_tarski(X7,X8) = k2_xboole_0(k1_tarski(X7),k2_tarski(X7,X8)) ),
    inference(superposition,[],[f275,f54])).

fof(f54,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f275,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X2,X1),X1) = X1 ),
    inference(superposition,[],[f268,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f268,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1 ),
    inference(superposition,[],[f264,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f264,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(backward_demodulation,[],[f135,f244])).

fof(f244,plain,(
    ! [X6,X5] : k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,X6)) = X5 ),
    inference(superposition,[],[f224,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f224,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X9,X10),X10) = X9 ),
    inference(superposition,[],[f201,f197])).

fof(f197,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f173,f80])).

fof(f80,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f79,f34])).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f79,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f78,f28])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f78,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f37,f74])).

fof(f74,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f38,f58])).

fof(f58,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f56,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f56,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f37,f29])).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f173,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f42,f138])).

fof(f138,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f71,f137])).

fof(f137,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f130,f86])).

fof(f86,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f84,f49])).

fof(f49,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(superposition,[],[f35,f33])).

fof(f84,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f56,f80])).

fof(f130,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f39,f29])).

fof(f71,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f38,f31])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f201,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f197,f34])).

fof(f135,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f37,f39])).

fof(f27,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25])).

fof(f25,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 12:27:45 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.51  % (6730)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.52  % (6736)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.23/0.52  % (6738)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.52  % (6734)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.52  % (6735)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.23/0.52  % (6744)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.23/0.52  % (6740)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.23/0.53  % (6733)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.53  % (6732)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.53  % (6742)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.53  % (6743)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.54  % (6744)Refutation found. Thanks to Tanya!
% 0.23/0.54  % SZS status Theorem for theBenchmark
% 0.23/0.54  % SZS output start Proof for theBenchmark
% 0.23/0.54  fof(f290,plain,(
% 0.23/0.54    $false),
% 0.23/0.54    inference(subsumption_resolution,[],[f27,f287])).
% 0.23/0.54  fof(f287,plain,(
% 0.23/0.54    ( ! [X8,X7] : (k2_tarski(X7,X8) = k2_xboole_0(k1_tarski(X7),k2_tarski(X7,X8))) )),
% 0.23/0.54    inference(superposition,[],[f275,f54])).
% 0.23/0.54  fof(f54,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.23/0.54    inference(resolution,[],[f40,f32])).
% 0.23/0.54  fof(f32,plain,(
% 0.23/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f19])).
% 0.23/0.54  fof(f19,axiom,(
% 0.23/0.54    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.23/0.54  fof(f40,plain,(
% 0.23/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f24])).
% 0.23/0.54  fof(f24,plain,(
% 0.23/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.23/0.54    inference(ennf_transformation,[],[f7])).
% 0.23/0.54  fof(f7,axiom,(
% 0.23/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.23/0.54  fof(f275,plain,(
% 0.23/0.54    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X2,X1),X1) = X1) )),
% 0.23/0.54    inference(superposition,[],[f268,f33])).
% 0.23/0.54  fof(f33,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f1])).
% 0.23/0.54  fof(f1,axiom,(
% 0.23/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.54  fof(f268,plain,(
% 0.23/0.54    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1) )),
% 0.23/0.54    inference(superposition,[],[f264,f39])).
% 0.23/0.54  fof(f39,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f9])).
% 0.23/0.54  fof(f9,axiom,(
% 0.23/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.54  fof(f264,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 0.23/0.54    inference(backward_demodulation,[],[f135,f244])).
% 0.23/0.54  fof(f244,plain,(
% 0.23/0.54    ( ! [X6,X5] : (k5_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(X5,X6)) = X5) )),
% 0.23/0.54    inference(superposition,[],[f224,f38])).
% 0.23/0.54  fof(f38,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f4])).
% 0.23/0.54  fof(f4,axiom,(
% 0.23/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.23/0.54  fof(f224,plain,(
% 0.23/0.54    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X9,X10),X10) = X9) )),
% 0.23/0.54    inference(superposition,[],[f201,f197])).
% 0.23/0.54  fof(f197,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.23/0.54    inference(forward_demodulation,[],[f173,f80])).
% 0.23/0.54  fof(f80,plain,(
% 0.23/0.54    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.23/0.54    inference(superposition,[],[f79,f34])).
% 0.23/0.54  fof(f34,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.23/0.54    inference(cnf_transformation,[],[f2])).
% 0.23/0.54  fof(f2,axiom,(
% 0.23/0.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.23/0.54  fof(f79,plain,(
% 0.23/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.54    inference(forward_demodulation,[],[f78,f28])).
% 0.23/0.54  fof(f28,plain,(
% 0.23/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f5])).
% 0.23/0.54  fof(f5,axiom,(
% 0.23/0.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.23/0.54  fof(f78,plain,(
% 0.23/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.54    inference(superposition,[],[f37,f74])).
% 0.23/0.54  fof(f74,plain,(
% 0.23/0.54    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6)) )),
% 0.23/0.54    inference(superposition,[],[f38,f58])).
% 0.23/0.54  fof(f58,plain,(
% 0.23/0.54    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) )),
% 0.23/0.54    inference(superposition,[],[f56,f35])).
% 0.23/0.54  fof(f35,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f6])).
% 0.23/0.54  fof(f6,axiom,(
% 0.23/0.54    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.23/0.54  fof(f56,plain,(
% 0.23/0.54    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.23/0.54    inference(superposition,[],[f37,f29])).
% 0.23/0.54  fof(f29,plain,(
% 0.23/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f8])).
% 0.23/0.54  fof(f8,axiom,(
% 0.23/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.23/0.54  fof(f37,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f11])).
% 0.23/0.54  fof(f11,axiom,(
% 0.23/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.23/0.54  fof(f173,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.23/0.54    inference(superposition,[],[f42,f138])).
% 0.23/0.54  fof(f138,plain,(
% 0.23/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.23/0.54    inference(backward_demodulation,[],[f71,f137])).
% 0.23/0.54  fof(f137,plain,(
% 0.23/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.23/0.54    inference(forward_demodulation,[],[f130,f86])).
% 0.23/0.54  fof(f86,plain,(
% 0.23/0.54    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) )),
% 0.23/0.54    inference(superposition,[],[f84,f49])).
% 0.23/0.54  fof(f49,plain,(
% 0.23/0.54    ( ! [X2,X1] : (k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1) )),
% 0.23/0.54    inference(superposition,[],[f35,f33])).
% 0.23/0.54  fof(f84,plain,(
% 0.23/0.54    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.23/0.54    inference(backward_demodulation,[],[f56,f80])).
% 0.23/0.54  fof(f130,plain,(
% 0.23/0.54    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.23/0.54    inference(superposition,[],[f39,f29])).
% 0.23/0.54  fof(f71,plain,(
% 0.23/0.54    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 0.23/0.54    inference(superposition,[],[f38,f31])).
% 0.23/0.54  fof(f31,plain,(
% 0.23/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.23/0.54    inference(cnf_transformation,[],[f22])).
% 0.23/0.54  fof(f22,plain,(
% 0.23/0.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.23/0.54    inference(rectify,[],[f3])).
% 0.23/0.54  fof(f3,axiom,(
% 0.23/0.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.23/0.54  fof(f42,plain,(
% 0.23/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.23/0.54    inference(cnf_transformation,[],[f10])).
% 0.23/0.54  fof(f10,axiom,(
% 0.23/0.54    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.23/0.54  fof(f201,plain,(
% 0.23/0.54    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 0.23/0.54    inference(superposition,[],[f197,f34])).
% 0.23/0.54  fof(f135,plain,(
% 0.23/0.54    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.23/0.54    inference(superposition,[],[f37,f39])).
% 0.23/0.54  fof(f27,plain,(
% 0.23/0.54    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.23/0.54    inference(cnf_transformation,[],[f26])).
% 0.23/0.54  fof(f26,plain,(
% 0.23/0.54    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25])).
% 0.23/0.54  fof(f25,plain,(
% 0.23/0.54    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.23/0.54    introduced(choice_axiom,[])).
% 0.23/0.54  fof(f23,plain,(
% 0.23/0.54    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.23/0.54    inference(ennf_transformation,[],[f21])).
% 0.23/0.54  fof(f21,negated_conjecture,(
% 0.23/0.54    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.23/0.54    inference(negated_conjecture,[],[f20])).
% 0.23/0.54  fof(f20,conjecture,(
% 0.23/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 0.23/0.54  % SZS output end Proof for theBenchmark
% 0.23/0.54  % (6744)------------------------------
% 0.23/0.54  % (6744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (6744)Termination reason: Refutation
% 0.23/0.54  
% 0.23/0.54  % (6744)Memory used [KB]: 6268
% 0.23/0.54  % (6744)Time elapsed: 0.094 s
% 0.23/0.54  % (6744)------------------------------
% 0.23/0.54  % (6744)------------------------------
% 0.23/0.55  % (6727)Success in time 0.168 s
%------------------------------------------------------------------------------
