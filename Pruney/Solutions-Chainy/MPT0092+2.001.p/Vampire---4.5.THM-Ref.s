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
% DateTime   : Thu Dec  3 12:31:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  86 expanded)
%              Number of leaves         :   11 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :   64 ( 126 expanded)
%              Number of equality atoms :   35 (  68 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1850,plain,(
    $false ),
    inference(resolution,[],[f1837,f20])).

fof(f20,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f1837,plain,(
    ! [X11] : r1_xboole_0(sK0,k4_xboole_0(X11,sK1)) ),
    inference(trivial_inequality_removal,[],[f1823])).

fof(f1823,plain,(
    ! [X11] :
      ( sK0 != sK0
      | r1_xboole_0(sK0,k4_xboole_0(X11,sK1)) ) ),
    inference(superposition,[],[f29,f1786])).

fof(f1786,plain,(
    ! [X13] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X13,sK1)) ),
    inference(forward_demodulation,[],[f1693,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1693,plain,(
    ! [X13] : k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(X13,sK1)) ),
    inference(superposition,[],[f204,f131])).

fof(f131,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f92,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f92,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,X7)) ),
    inference(backward_demodulation,[],[f73,f90])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f85,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f85,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(superposition,[],[f23,f51])).

fof(f51,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(resolution,[],[f31,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f73,plain,(
    ! [X7] : k4_xboole_0(sK0,k2_xboole_0(sK1,X7)) = k4_xboole_0(k1_xboole_0,X7) ),
    inference(superposition,[],[f33,f49])).

fof(f49,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f31,f19])).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f204,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4))) ),
    inference(forward_demodulation,[],[f203,f38])).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f24,f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f203,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(X2,k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,X4))) ),
    inference(forward_demodulation,[],[f168,f51])).

fof(f168,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X2),k4_xboole_0(X3,X4))) = k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4))) ),
    inference(superposition,[],[f36,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f35,f33])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f32,f25,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n021.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 17:42:19 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.47  % (23974)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (23989)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (23976)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (23973)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (23983)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (23975)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (23982)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (23972)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (23981)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (23978)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (23977)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (23988)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (23979)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (23980)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (23986)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (23987)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (23984)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.53  % (23985)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.54  % (23973)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f1850,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(resolution,[],[f1837,f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.54    inference(negated_conjecture,[],[f12])).
% 0.21/0.54  fof(f12,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.21/0.54  fof(f1837,plain,(
% 0.21/0.54    ( ! [X11] : (r1_xboole_0(sK0,k4_xboole_0(X11,sK1))) )),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f1823])).
% 0.21/0.54  fof(f1823,plain,(
% 0.21/0.54    ( ! [X11] : (sK0 != sK0 | r1_xboole_0(sK0,k4_xboole_0(X11,sK1))) )),
% 0.21/0.54    inference(superposition,[],[f29,f1786])).
% 0.21/0.54  fof(f1786,plain,(
% 0.21/0.54    ( ! [X13] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X13,sK1))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f1693,f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.54  fof(f1693,plain,(
% 0.21/0.54    ( ! [X13] : (k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(X13,sK1))) )),
% 0.21/0.54    inference(superposition,[],[f204,f131])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X0,sK1))) )),
% 0.21/0.54    inference(superposition,[],[f92,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,X7))) )),
% 0.21/0.54    inference(backward_demodulation,[],[f73,f90])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(resolution,[],[f85,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X4] : (r1_tarski(k1_xboole_0,X4)) )),
% 0.21/0.54    inference(superposition,[],[f23,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 0.21/0.54    inference(resolution,[],[f31,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.54    inference(superposition,[],[f23,f22])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X7] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X7)) = k4_xboole_0(k1_xboole_0,X7)) )),
% 0.21/0.54    inference(superposition,[],[f33,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f31,f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.54  fof(f204,plain,(
% 0.21/0.54    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f203,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.54    inference(superposition,[],[f24,f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.54  fof(f203,plain,(
% 0.21/0.54    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(X2,k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,X4)))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f168,f51])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X2),k4_xboole_0(X3,X4))) = k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4)))) )),
% 0.21/0.54    inference(superposition,[],[f36,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 0.21/0.54    inference(backward_demodulation,[],[f35,f33])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f32,f25,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (23973)------------------------------
% 0.21/0.54  % (23973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23973)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (23973)Memory used [KB]: 3198
% 0.21/0.54  % (23973)Time elapsed: 0.132 s
% 0.21/0.54  % (23973)------------------------------
% 0.21/0.54  % (23973)------------------------------
% 0.21/0.54  % (23970)Success in time 0.186 s
%------------------------------------------------------------------------------
