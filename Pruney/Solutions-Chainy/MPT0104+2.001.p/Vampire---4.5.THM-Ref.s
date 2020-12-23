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
% DateTime   : Thu Dec  3 12:32:01 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   45 (  95 expanded)
%              Number of leaves         :    9 (  26 expanded)
%              Depth                    :   16
%              Number of atoms          :   74 ( 201 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1424,plain,(
    $false ),
    inference(subsumption_resolution,[],[f53,f1416])).

fof(f1416,plain,(
    ~ r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f195,f1358])).

fof(f1358,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f28,f49])).

fof(f49,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f27,f21])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f195,plain,(
    ~ r1_tarski(k4_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK2,k5_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f194,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f194,plain,(
    ~ r1_tarski(k4_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(k5_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f187,f28])).

fof(f187,plain,(
    ~ r1_tarski(k4_xboole_0(k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),sK2),k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f154,f169])).

fof(f169,plain,(
    ~ r1_tarski(k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),sK2) ),
    inference(forward_demodulation,[],[f168,f23])).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f168,plain,(
    ~ r1_tarski(k4_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK2) ),
    inference(forward_demodulation,[],[f167,f28])).

fof(f167,plain,(
    ~ r1_tarski(k4_xboole_0(k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)),sK2) ),
    inference(resolution,[],[f145,f158])).

fof(f158,plain,(
    ~ r1_tarski(k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK2) ),
    inference(resolution,[],[f144,f20])).

fof(f20,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2)
    & r1_tarski(k4_xboole_0(sK1,sK0),sK2)
    & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
        & r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2)
      & r1_tarski(k4_xboole_0(sK1,sK0),sK2)
      & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
      & r1_tarski(k4_xboole_0(X1,X0),X2)
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
      & r1_tarski(k4_xboole_0(X1,X0),X2)
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
          & r1_tarski(k4_xboole_0(X0,X1),X2) )
       => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
     => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).

fof(f144,plain,(
    ! [X9] :
      ( r1_tarski(X9,sK2)
      | ~ r1_tarski(k4_xboole_0(X9,k4_xboole_0(sK0,sK1)),sK2) ) ),
    inference(superposition,[],[f29,f30])).

fof(f30,plain,(
    sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(resolution,[],[f25,f18])).

fof(f18,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f145,plain,(
    ! [X10] :
      ( r1_tarski(X10,sK2)
      | ~ r1_tarski(k4_xboole_0(X10,k4_xboole_0(sK1,sK0)),sK2) ) ),
    inference(superposition,[],[f29,f31])).

fof(f31,plain,(
    sK2 = k2_xboole_0(k4_xboole_0(sK1,sK0),sK2) ),
    inference(resolution,[],[f25,f19])).

fof(f19,plain,(
    r1_tarski(k4_xboole_0(sK1,sK0),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f154,plain,(
    ! [X25] :
      ( r1_tarski(X25,sK2)
      | ~ r1_tarski(k4_xboole_0(X25,sK2),k4_xboole_0(sK0,sK1)) ) ),
    inference(superposition,[],[f29,f33])).

fof(f33,plain,(
    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f30,f22])).

fof(f53,plain,(
    r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f21,f47])).

fof(f47,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(resolution,[],[f27,f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.43  % (13553)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.43  % (13544)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.45  % (13551)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.46  % (13555)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.46  % (13550)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.46  % (13552)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.46  % (13538)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.46  % (13543)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.47  % (13545)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.47  % (13539)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.47  % (13548)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.48  % (13540)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.48  % (13547)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.48  % (13546)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.49  % (13541)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.49  % (13549)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.49  % (13554)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.51  % (13542)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.54  % (13554)Refutation found. Thanks to Tanya!
% 0.19/0.54  % SZS status Theorem for theBenchmark
% 0.19/0.54  % SZS output start Proof for theBenchmark
% 0.19/0.54  fof(f1424,plain,(
% 0.19/0.54    $false),
% 0.19/0.54    inference(subsumption_resolution,[],[f53,f1416])).
% 0.19/0.54  fof(f1416,plain,(
% 0.19/0.54    ~r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 0.19/0.54    inference(backward_demodulation,[],[f195,f1358])).
% 0.19/0.54  fof(f1358,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 0.19/0.54    inference(superposition,[],[f28,f49])).
% 0.19/0.54  fof(f49,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.19/0.54    inference(resolution,[],[f27,f21])).
% 0.19/0.54  fof(f21,plain,(
% 0.19/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f6])).
% 0.19/0.54  fof(f6,axiom,(
% 0.19/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.19/0.54  fof(f27,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.19/0.54    inference(cnf_transformation,[],[f17])).
% 0.19/0.54  fof(f17,plain,(
% 0.19/0.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.19/0.54    inference(nnf_transformation,[],[f3])).
% 0.19/0.54  fof(f3,axiom,(
% 0.19/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.19/0.54  fof(f28,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f7])).
% 0.19/0.54  fof(f7,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.19/0.54  fof(f195,plain,(
% 0.19/0.54    ~r1_tarski(k4_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK2,k5_xboole_0(sK0,sK1))),k4_xboole_0(sK0,sK1))),
% 0.19/0.54    inference(forward_demodulation,[],[f194,f22])).
% 0.19/0.54  fof(f22,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f1])).
% 0.19/0.54  fof(f1,axiom,(
% 0.19/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.54  fof(f194,plain,(
% 0.19/0.54    ~r1_tarski(k4_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(k5_xboole_0(sK0,sK1),sK2)),k4_xboole_0(sK0,sK1))),
% 0.19/0.54    inference(forward_demodulation,[],[f187,f28])).
% 0.19/0.54  fof(f187,plain,(
% 0.19/0.54    ~r1_tarski(k4_xboole_0(k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),sK2),k4_xboole_0(sK0,sK1))),
% 0.19/0.54    inference(resolution,[],[f154,f169])).
% 0.19/0.54  fof(f169,plain,(
% 0.19/0.54    ~r1_tarski(k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),sK2)),
% 0.19/0.54    inference(forward_demodulation,[],[f168,f23])).
% 0.19/0.54  fof(f23,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f2])).
% 0.19/0.54  fof(f2,axiom,(
% 0.19/0.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.19/0.54  fof(f168,plain,(
% 0.19/0.54    ~r1_tarski(k4_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK2)),
% 0.19/0.54    inference(forward_demodulation,[],[f167,f28])).
% 0.19/0.54  fof(f167,plain,(
% 0.19/0.54    ~r1_tarski(k4_xboole_0(k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)),sK2)),
% 0.19/0.54    inference(resolution,[],[f145,f158])).
% 0.19/0.54  fof(f158,plain,(
% 0.19/0.54    ~r1_tarski(k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK2)),
% 0.19/0.54    inference(resolution,[],[f144,f20])).
% 0.19/0.54  fof(f20,plain,(
% 0.19/0.54    ~r1_tarski(k5_xboole_0(sK0,sK1),sK2)),
% 0.19/0.54    inference(cnf_transformation,[],[f16])).
% 0.19/0.54  fof(f16,plain,(
% 0.19/0.54    ~r1_tarski(k5_xboole_0(sK0,sK1),sK2) & r1_tarski(k4_xboole_0(sK1,sK0),sK2) & r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.19/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 0.19/0.54  fof(f15,plain,(
% 0.19/0.54    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => (~r1_tarski(k5_xboole_0(sK0,sK1),sK2) & r1_tarski(k4_xboole_0(sK1,sK0),sK2) & r1_tarski(k4_xboole_0(sK0,sK1),sK2))),
% 0.19/0.54    introduced(choice_axiom,[])).
% 0.19/0.54  fof(f12,plain,(
% 0.19/0.54    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.19/0.54    inference(flattening,[],[f11])).
% 0.19/0.54  fof(f11,plain,(
% 0.19/0.54    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & (r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)))),
% 0.19/0.54    inference(ennf_transformation,[],[f10])).
% 0.19/0.54  fof(f10,negated_conjecture,(
% 0.19/0.54    ~! [X0,X1,X2] : ((r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => r1_tarski(k5_xboole_0(X0,X1),X2))),
% 0.19/0.54    inference(negated_conjecture,[],[f9])).
% 0.19/0.54  fof(f9,conjecture,(
% 0.19/0.54    ! [X0,X1,X2] : ((r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => r1_tarski(k5_xboole_0(X0,X1),X2))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).
% 0.19/0.54  fof(f144,plain,(
% 0.19/0.54    ( ! [X9] : (r1_tarski(X9,sK2) | ~r1_tarski(k4_xboole_0(X9,k4_xboole_0(sK0,sK1)),sK2)) )),
% 0.19/0.54    inference(superposition,[],[f29,f30])).
% 0.19/0.54  fof(f30,plain,(
% 0.19/0.54    sK2 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 0.19/0.54    inference(resolution,[],[f25,f18])).
% 0.19/0.54  fof(f18,plain,(
% 0.19/0.54    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.19/0.54    inference(cnf_transformation,[],[f16])).
% 0.19/0.54  fof(f25,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.19/0.54    inference(cnf_transformation,[],[f13])).
% 0.19/0.54  fof(f13,plain,(
% 0.19/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.54    inference(ennf_transformation,[],[f5])).
% 0.19/0.54  fof(f5,axiom,(
% 0.19/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.54  fof(f29,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f14])).
% 0.19/0.54  fof(f14,plain,(
% 0.19/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.19/0.54    inference(ennf_transformation,[],[f8])).
% 0.19/0.54  fof(f8,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.19/0.54  fof(f145,plain,(
% 0.19/0.54    ( ! [X10] : (r1_tarski(X10,sK2) | ~r1_tarski(k4_xboole_0(X10,k4_xboole_0(sK1,sK0)),sK2)) )),
% 0.19/0.54    inference(superposition,[],[f29,f31])).
% 0.19/0.54  fof(f31,plain,(
% 0.19/0.54    sK2 = k2_xboole_0(k4_xboole_0(sK1,sK0),sK2)),
% 0.19/0.54    inference(resolution,[],[f25,f19])).
% 0.19/0.54  fof(f19,plain,(
% 0.19/0.54    r1_tarski(k4_xboole_0(sK1,sK0),sK2)),
% 0.19/0.54    inference(cnf_transformation,[],[f16])).
% 0.19/0.54  fof(f154,plain,(
% 0.19/0.54    ( ! [X25] : (r1_tarski(X25,sK2) | ~r1_tarski(k4_xboole_0(X25,sK2),k4_xboole_0(sK0,sK1))) )),
% 0.19/0.54    inference(superposition,[],[f29,f33])).
% 0.19/0.54  fof(f33,plain,(
% 0.19/0.54    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 0.19/0.54    inference(superposition,[],[f30,f22])).
% 0.19/0.54  fof(f53,plain,(
% 0.19/0.54    r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 0.19/0.54    inference(superposition,[],[f21,f47])).
% 0.19/0.54  fof(f47,plain,(
% 0.19/0.54    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 0.19/0.54    inference(resolution,[],[f27,f18])).
% 0.19/0.54  % SZS output end Proof for theBenchmark
% 0.19/0.54  % (13554)------------------------------
% 0.19/0.54  % (13554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (13554)Termination reason: Refutation
% 0.19/0.54  
% 0.19/0.54  % (13554)Memory used [KB]: 7036
% 0.19/0.54  % (13554)Time elapsed: 0.147 s
% 0.19/0.54  % (13554)------------------------------
% 0.19/0.54  % (13554)------------------------------
% 0.19/0.56  % (13537)Success in time 0.207 s
%------------------------------------------------------------------------------
