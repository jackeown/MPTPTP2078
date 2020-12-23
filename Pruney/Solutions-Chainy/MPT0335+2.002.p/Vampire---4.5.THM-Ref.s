%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:15 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 152 expanded)
%              Number of leaves         :    8 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :   78 ( 382 expanded)
%              Number of equality atoms :   49 ( 220 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1028,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1015,f54])).

fof(f54,plain,(
    k1_tarski(sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
      & r2_hidden(sK3,sK0)
      & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f1015,plain,(
    k1_tarski(sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f251,f951])).

fof(f951,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f927,f883])).

fof(f883,plain,(
    ! [X31] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X31))) = k4_xboole_0(sK0,X31) ),
    inference(forward_demodulation,[],[f882,f58])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f882,plain,(
    ! [X31] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X31))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X31))) ),
    inference(forward_demodulation,[],[f801,f82])).

fof(f82,plain,(
    sK0 = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f81,f77])).

fof(f77,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f49,f30])).

fof(f30,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f81,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f64,f30])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f47,f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f801,plain,(
    ! [X31] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X31))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,X31))) ),
    inference(superposition,[],[f65,f77])).

fof(f65,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f50,f39,f39,f39])).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f927,plain,(
    k4_xboole_0(sK0,k1_tarski(sK3)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f883,f127])).

fof(f127,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_tarski(sK3)) ),
    inference(superposition,[],[f58,f55])).

fof(f55,plain,(
    k1_tarski(sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(definition_unfolding,[],[f31,f39])).

fof(f31,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f251,plain,(
    k1_tarski(sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_tarski(sK3))) ),
    inference(resolution,[],[f62,f32])).

fof(f32,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0))) ) ),
    inference(definition_unfolding,[],[f45,f39])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:32:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (5595)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (5593)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (5591)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (5592)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (5604)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (5605)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (5596)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (5603)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (5597)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (5601)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (5600)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (5599)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (5594)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (5589)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (5606)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (5602)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (5590)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.23/0.51  % (5601)Refutation found. Thanks to Tanya!
% 1.23/0.51  % SZS status Theorem for theBenchmark
% 1.23/0.51  % SZS output start Proof for theBenchmark
% 1.23/0.51  fof(f1028,plain,(
% 1.23/0.51    $false),
% 1.23/0.51    inference(subsumption_resolution,[],[f1015,f54])).
% 1.23/0.51  fof(f54,plain,(
% 1.23/0.51    k1_tarski(sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.23/0.51    inference(definition_unfolding,[],[f33,f39])).
% 1.23/0.51  fof(f39,plain,(
% 1.23/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.23/0.51    inference(cnf_transformation,[],[f10])).
% 1.23/0.51  fof(f10,axiom,(
% 1.23/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.23/0.51  fof(f33,plain,(
% 1.23/0.51    k3_xboole_0(sK0,sK2) != k1_tarski(sK3)),
% 1.23/0.51    inference(cnf_transformation,[],[f28])).
% 1.23/0.51  fof(f28,plain,(
% 1.23/0.51    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 1.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f27])).
% 1.23/0.51  fof(f27,plain,(
% 1.23/0.51    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 1.23/0.51    introduced(choice_axiom,[])).
% 1.23/0.51  fof(f22,plain,(
% 1.23/0.51    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 1.23/0.51    inference(flattening,[],[f21])).
% 1.23/0.51  fof(f21,plain,(
% 1.23/0.51    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 1.23/0.51    inference(ennf_transformation,[],[f20])).
% 1.23/0.51  fof(f20,negated_conjecture,(
% 1.23/0.51    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 1.23/0.51    inference(negated_conjecture,[],[f19])).
% 1.23/0.51  fof(f19,conjecture,(
% 1.23/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 1.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 1.23/0.51  fof(f1015,plain,(
% 1.23/0.51    k1_tarski(sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.23/0.51    inference(backward_demodulation,[],[f251,f951])).
% 1.23/0.51  fof(f951,plain,(
% 1.23/0.51    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_tarski(sK3))),
% 1.23/0.51    inference(forward_demodulation,[],[f927,f883])).
% 1.23/0.51  fof(f883,plain,(
% 1.23/0.51    ( ! [X31] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X31))) = k4_xboole_0(sK0,X31)) )),
% 1.23/0.51    inference(forward_demodulation,[],[f882,f58])).
% 1.23/0.51  fof(f58,plain,(
% 1.23/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.23/0.51    inference(definition_unfolding,[],[f40,f39])).
% 1.23/0.51  fof(f40,plain,(
% 1.23/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.23/0.51    inference(cnf_transformation,[],[f9])).
% 1.23/0.51  fof(f9,axiom,(
% 1.23/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.23/0.51  fof(f882,plain,(
% 1.23/0.51    ( ! [X31] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X31))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X31)))) )),
% 1.23/0.51    inference(forward_demodulation,[],[f801,f82])).
% 1.23/0.51  fof(f82,plain,(
% 1.23/0.51    sK0 = k4_xboole_0(sK0,k1_xboole_0)),
% 1.23/0.51    inference(forward_demodulation,[],[f81,f77])).
% 1.23/0.51  fof(f77,plain,(
% 1.23/0.51    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.23/0.51    inference(resolution,[],[f49,f30])).
% 1.23/0.51  fof(f30,plain,(
% 1.23/0.51    r1_tarski(sK0,sK1)),
% 1.23/0.51    inference(cnf_transformation,[],[f28])).
% 1.23/0.51  fof(f49,plain,(
% 1.23/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.23/0.51    inference(cnf_transformation,[],[f29])).
% 1.23/0.51  fof(f29,plain,(
% 1.23/0.51    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.23/0.51    inference(nnf_transformation,[],[f5])).
% 1.23/0.51  fof(f5,axiom,(
% 1.23/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.23/0.51  fof(f81,plain,(
% 1.23/0.51    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.23/0.51    inference(resolution,[],[f64,f30])).
% 1.23/0.51  fof(f64,plain,(
% 1.23/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.23/0.51    inference(definition_unfolding,[],[f47,f39])).
% 1.23/0.51  fof(f47,plain,(
% 1.23/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.23/0.51    inference(cnf_transformation,[],[f26])).
% 1.23/0.51  fof(f26,plain,(
% 1.23/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.23/0.51    inference(ennf_transformation,[],[f8])).
% 1.23/0.51  fof(f8,axiom,(
% 1.23/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.23/0.51  fof(f801,plain,(
% 1.23/0.51    ( ! [X31] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X31))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,X31)))) )),
% 1.23/0.51    inference(superposition,[],[f65,f77])).
% 1.23/0.51  fof(f65,plain,(
% 1.23/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 1.23/0.51    inference(definition_unfolding,[],[f50,f39,f39,f39])).
% 1.23/0.51  fof(f50,plain,(
% 1.23/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.23/0.51    inference(cnf_transformation,[],[f11])).
% 1.23/0.51  fof(f11,axiom,(
% 1.23/0.51    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).
% 1.23/0.51  fof(f927,plain,(
% 1.23/0.51    k4_xboole_0(sK0,k1_tarski(sK3)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.23/0.51    inference(superposition,[],[f883,f127])).
% 1.23/0.51  fof(f127,plain,(
% 1.23/0.51    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_tarski(sK3))),
% 1.23/0.51    inference(superposition,[],[f58,f55])).
% 1.23/0.51  fof(f55,plain,(
% 1.23/0.51    k1_tarski(sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.23/0.51    inference(definition_unfolding,[],[f31,f39])).
% 1.23/0.51  fof(f31,plain,(
% 1.23/0.51    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 1.23/0.51    inference(cnf_transformation,[],[f28])).
% 1.23/0.51  fof(f251,plain,(
% 1.23/0.51    k1_tarski(sK3) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_tarski(sK3)))),
% 1.23/0.51    inference(resolution,[],[f62,f32])).
% 1.23/0.51  fof(f32,plain,(
% 1.23/0.51    r2_hidden(sK3,sK0)),
% 1.23/0.51    inference(cnf_transformation,[],[f28])).
% 1.23/0.51  fof(f62,plain,(
% 1.23/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(X1,k4_xboole_0(X1,k1_tarski(X0)))) )),
% 1.23/0.51    inference(definition_unfolding,[],[f45,f39])).
% 1.23/0.51  fof(f45,plain,(
% 1.23/0.51    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 1.23/0.51    inference(cnf_transformation,[],[f24])).
% 1.23/0.51  fof(f24,plain,(
% 1.23/0.51    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 1.23/0.51    inference(ennf_transformation,[],[f18])).
% 1.23/0.51  fof(f18,axiom,(
% 1.23/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 1.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).
% 1.23/0.51  % SZS output end Proof for theBenchmark
% 1.23/0.51  % (5601)------------------------------
% 1.23/0.51  % (5601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.51  % (5601)Termination reason: Refutation
% 1.23/0.51  
% 1.23/0.51  % (5601)Memory used [KB]: 2174
% 1.23/0.51  % (5601)Time elapsed: 0.090 s
% 1.23/0.51  % (5601)------------------------------
% 1.23/0.51  % (5601)------------------------------
% 1.23/0.52  % (5588)Success in time 0.156 s
%------------------------------------------------------------------------------
